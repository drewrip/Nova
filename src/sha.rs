//! Poseidon Constants and Poseidon-based RO used in Nova
use super::traits::{ROCircuitTrait, ROConstantsTrait, ROTrait};
use bellperson::{
  gadgets::{
    boolean::{AllocatedBit, Boolean},
    num::AllocatedNum,
    sha256::sha256,
  },
  ConstraintSystem, SynthesisError,
};
use bitvec::{
  view::BitView,
  prelude::Lsb0,
};
use core::marker::PhantomData;
use ff::{
  PrimeField, PrimeFieldBits,
};
use sha2::{Digest, Sha256};

/// All Poseidon Constants that are used in Nova
#[derive(Clone)]
pub struct Sha256ConstantsCircuit<Scalar: PrimeField>(Scalar);

impl<Scalar> ROConstantsTrait<Scalar> for Sha256ConstantsCircuit<Scalar>
where
  Scalar: PrimeField + PrimeFieldBits,
{
  /// Generate Poseidon constants
  #[allow(clippy::new_without_default)]
  fn new() -> Self {
    Self(Scalar::zero())
  }
}

/// A Poseidon-based RO to use outside circuits
pub struct Sha256RO<Base, Scalar>
where
  Base: PrimeField + PrimeFieldBits,
  Scalar: PrimeField + PrimeFieldBits,
{
  // Internal State
  state: Vec<Base>,
  constants: Sha256ConstantsCircuit<Base>,
  num_absorbs: usize,
  squeezed: bool,
  _p: PhantomData<Scalar>,
}

impl<Base, Scalar> ROTrait<Base, Scalar> for Sha256RO<Base, Scalar>
where
  Base: PrimeField + PrimeFieldBits,
  Scalar: PrimeField + PrimeFieldBits,
{
  type Constants = Sha256ConstantsCircuit<Base>;

  fn new(constants: Sha256ConstantsCircuit<Base>, num_absorbs: usize) -> Self {
    Self {
      state: Vec::new(),
      constants,
      num_absorbs,
      squeezed: false,
      _p: PhantomData::default(),
    }
  }

  /// Absorb a new number into the state of the oracle
  fn absorb(&mut self, e: Base) {
    assert!(!self.squeezed, "Cannot absorb after squeezing");
    self.state.push(e);
  }

  /// Compute a challenge by hashing the current state
  fn squeeze(&mut self, num_bits: usize) -> Scalar {
    // check if we have squeezed already
    assert!(!self.squeezed, "Cannot squeeze again after squeezing");
    self.squeezed = true;

    let mut hasher = Sha256::new();
    assert_eq!(self.num_absorbs, self.state.len());

    let data = self.state.iter().map(
      |b| {
        (*b).to_repr().as_ref().to_vec()
      }
    ).collect::<Vec<Vec<u8>>>().concat();

    hasher.update(data);

    let hash_output = hasher.finalize();
    let hash: &[u8] = hash_output.as_ref();
    assert_eq!(hash.len(), 32);
    
    // Only return `num_bits`
    let bits = hash.view_bits::<Lsb0>();
    let mut res = Scalar::zero();
    let mut coeff = Scalar::one();
    for bit in bits[0..num_bits].into_iter() {
      if *bit {
        res += coeff;
      }
      coeff += coeff;
    }
    res
  }
}

/// A Poseidon-based RO gadget to use inside the verifier circuit.
pub struct Sha256ROCircuit<Scalar>
where
  Scalar: PrimeField + PrimeFieldBits,
{
  // Internal state
  state: Vec<AllocatedNum<Scalar>>,
  constants: Sha256ConstantsCircuit<Scalar>,
  num_absorbs: usize,
  squeezed: bool,
}

impl<Scalar> ROCircuitTrait<Scalar> for Sha256ROCircuit<Scalar>
where
  Scalar: PrimeField + PrimeFieldBits,
{
  type Constants = Sha256ConstantsCircuit<Scalar>;

  /// Initialize the internal state and set the poseidon constants
  fn new(constants: Sha256ConstantsCircuit<Scalar>, num_absorbs: usize) -> Self {
    Self {
      state: Vec::new(),
      constants,
      num_absorbs,
      squeezed: false,
    }
  }

  /// Absorb a new number into the state of the oracle
  fn absorb(&mut self, e: AllocatedNum<Scalar>) {
    assert!(!self.squeezed, "Cannot absorb after squeezing");
    self.state.push(e);
  }

  /// Compute a challenge by hashing the current state
  fn squeeze<CS>(
    &mut self,
    mut cs: CS,
    num_bits: usize,
  ) -> Result<Vec<AllocatedBit>, SynthesisError>
  where
    CS: ConstraintSystem<Scalar>,
  {
    // check if we have squeezed already
    assert!(!self.squeezed, "Cannot squeeze again after squeezing");
    self.squeezed = true;

    let mut ns = cs.namespace(|| "ns");

    let scalar_bitstrings: Vec<Vec<Boolean>> = self.state
      .iter()
      .enumerate()
      .map(|(i, n)| {
        let alloc_scalar_bits = n.to_bits_le_strict(ns.namespace(|| format!("alloc scalar as bits {}", i)));
        match alloc_scalar_bits {
          Ok(v) => {
            let pad_bits: Vec<Boolean> = (0..(256-v.len()))
              .into_iter()
              .map(|j| {  
                let pad_bit = 
                  AllocatedBit::alloc(
                    ns.namespace(|| format!("allocating pad bit {}-{}", i, j)),
                    Some(false),
                  );
                match pad_bit {
                  Ok(b) => Boolean::from(b),
                  Err(_) => panic!("Error cannot allocate pad bit"),
                }
              })
              .collect::<Vec<Boolean>>();
            [v, pad_bits].concat()
          },
          Err(e) => panic!("Error in input bit of sha RO: {}", e),
        }
      })
      .collect::<Vec<Vec<Boolean>>>();

    let data: Vec<Boolean> = scalar_bitstrings
      .concat()
      .chunks(8)
      .map(|c| c.iter().rev())
      .flatten()
      .cloned()
      .collect();

    let hash = sha256(ns.namespace(|| "sha256(x)"), &data)?;

    // return the hash as a vector of bits, truncated
    Ok(
      hash
        .chunks(8)
        .map(|c| c.iter().rev())
        .flatten()
        .cloned()
        .map(|boolean| match boolean {
          Boolean::Is(ref x) => x.clone(),
          _ => panic!("Wrong type of input. We should have never reached there"),
        })
        .collect::<Vec<AllocatedBit>>()[..num_bits]
        .into(),
    )
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  type S = pasta_curves::pallas::Scalar;
  type B = pasta_curves::vesta::Scalar;
  type G = pasta_curves::pallas::Point;
  use crate::{
    bellperson::solver::SatisfyingAssignment, constants::NUM_CHALLENGE_BITS,
    gadgets::utils::le_bits_to_num,
  };
  use ff::Field;
  use rand::rngs::OsRng;

  #[test]
  fn test_Sha256_ro() {
    // Check that the number computed inside the circuit is equal to the number computed outside the circuit
    let mut csprng: OsRng = OsRng;
    let constants = Sha256ConstantsCircuit::new();
    let num_absorbs = 1;
    let mut ro: Sha256RO<S, B> = Sha256RO::new(constants.clone(), num_absorbs);
    let mut ro_gadget: Sha256ROCircuit<S> = Sha256ROCircuit::new(constants, num_absorbs);
    let mut cs: SatisfyingAssignment<G> = SatisfyingAssignment::new();
    for i in 0..num_absorbs {
      let num = S::random(&mut csprng);
      ro.absorb(num);
      let num_gadget =
        AllocatedNum::alloc(cs.namespace(|| format!("data {}", i)), || Ok(num)).unwrap();
      num_gadget
        .inputize(&mut cs.namespace(|| format!("input {}", i)))
        .unwrap();
      ro_gadget.absorb(num_gadget);
    }
    let num = ro.squeeze(NUM_CHALLENGE_BITS);
    let num2_bits = ro_gadget.squeeze(&mut cs, NUM_CHALLENGE_BITS).unwrap();
    let num2 = le_bits_to_num(&mut cs, num2_bits).unwrap();
    assert_eq!(num.to_repr(), num2.get_value().unwrap().to_repr());
  }
}
