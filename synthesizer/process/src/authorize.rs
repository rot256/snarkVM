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
use console::account::Address;

impl<N: Network> Process<N> {
    /// Authorizes a call to the program function for the given inputs.
    #[inline]
    pub fn authorize<A: circuit::Aleo<Network = N>, R: Rng + CryptoRng>(
        &self,
        private_key: &PrivateKey<N>,
        program_id: impl TryInto<ProgramID<N>>,
        function_name: impl TryInto<Identifier<N>>,
        inputs: impl ExactSizeIterator<Item = impl TryInto<Value<N>>>,
        rng: &mut R,
    ) -> Result<Authorization<N>> {
        // Authorize the call.
        self.get_stack(program_id)?.authorize::<A, R>(private_key, function_name, inputs, rng)
    }

    /// Authorizes the fee given the credits record, the fee amount (in microcredits),
    /// and the deployment or execution ID.
    #[inline]
    pub fn authorize_fee_private<R: Rng + CryptoRng>(
        &self,
        private_key: &PrivateKey<N>,
        credits: Record<N, Plaintext<N>>,
        fee_in_microcredits: u64,
        deployment_or_execution_id: Field<N>,
        rng: &mut R,
    ) -> Result<Authorization<N>> {
        let timer = timer!("Process::authorize_fee_private");

        // Derive the parent address from the private key.
        // TODO (@d0cd) Is this assumption valid?
        // This consistent since the entity invoking `authorize_fee_private` must be a user.
        let parent = Address::try_from(private_key)?;

        // Ensure the fee has the correct program ID.
        let program_id = ProgramID::from_str("credits.aleo")?;
        // Ensure the fee has the correct function.
        let function_name = Identifier::from_str("fee_private")?;
        // Retrieve the input types.
        let input_types = self.get_program(program_id)?.get_function(&function_name)?.input_types();

        // Ensure the record contains a sufficient balance to pay the fee.
        ensure_record_balance(&credits, fee_in_microcredits)?;

        // Construct the inputs.
        let inputs = [
            Value::Record(credits),
            Value::from(Literal::U64(U64::<N>::new(fee_in_microcredits))),
            Value::from(Literal::Field(deployment_or_execution_id)),
        ];
        lap!(timer, "Construct the inputs");

        // Compute the request.
        let request = Request::sign(private_key, parent, program_id, function_name, inputs.iter(), &input_types, rng)?;
        finish!(timer, "Compute the request");

        // Return the authorization.
        Ok(Authorization::from(request))
    }

    /// Authorizes the fee given the the fee amount (in microcredits) and the deployment or execution ID.
    #[inline]
    pub fn authorize_fee_public<R: Rng + CryptoRng>(
        &self,
        private_key: &PrivateKey<N>,
        fee_in_microcredits: u64,
        deployment_or_execution_id: Field<N>,
        rng: &mut R,
    ) -> Result<Authorization<N>> {
        let timer = timer!("Process::authorize_fee_public");

        // Derive the parent address from the private key.
        // TODO (@d0cd) Is this assumption valid?
        // This consistent since the entity invoking `authorize_fee_private` must be a user.
        let parent = Address::try_from(private_key)?;

        // Ensure the fee has the correct program ID.
        let program_id = ProgramID::from_str("credits.aleo")?;
        // Ensure the fee has the correct function.
        let function_name = Identifier::from_str("fee_public")?;
        // Construct the input types.
        let input_types = [ValueType::Public(LiteralType::U64.into()), ValueType::Public(LiteralType::Field.into())];
        // Construct the inputs.
        let inputs = [
            Value::from(Literal::U64(U64::<N>::new(fee_in_microcredits))),
            Value::from(Literal::Field(deployment_or_execution_id)),
        ];
        lap!(timer, "Construct the inputs");

        // Compute the request.
        let request = Request::sign(private_key, parent, program_id, function_name, inputs.iter(), &input_types, rng)?;
        finish!(timer, "Compute the request");

        // Return the authorization.
        Ok(Authorization::from(request))
    }
}

/// Ensures the record contains a sufficient balance to pay the fee.
fn ensure_record_balance<N: Network>(record: &Record<N, Plaintext<N>>, fee_in_microcredits: u64) -> Result<()> {
    // Retrieve the balance from the record.
    let balance = match record.find(&[Identifier::from_str("microcredits")?]) {
        Ok(console::program::Entry::Private(Plaintext::Literal(Literal::U64(amount), _))) => *amount,
        _ => bail!("The fee record does not contain a 'microcredits' entry"),
    };
    // Ensure the balance is sufficient to pay the fee.
    ensure!(balance >= fee_in_microcredits, "Credits record balance is insufficient to pay the fee");
    Ok(())
}
