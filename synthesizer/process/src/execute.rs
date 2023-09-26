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

impl<N: Network> Process<N> {
    /// Executes the given authorization.
    #[inline]
    pub fn execute<A: circuit::Aleo<Network = N>>(
        &self,
        authorization: Authorization<N>,
    ) -> Result<(Response<N>, Trace<N>)> {
        let timer = timer!("Process::execute");

        // Retrieve the main request (without popping it).
        let request = authorization.peek_next()?;
        // Construct the locator.
        let locator = Locator::new(*request.program_id(), *request.function_name());

        #[cfg(feature = "aleo-cli")]
        println!("{}", format!(" • Executing '{locator}'...",).dimmed());

        // Initialize the trace.
        let trace = Arc::new(RwLock::new(Trace::new()));
        // Initialize the call stack.
        let call_stack = CallStack::execute(authorization, trace.clone())?;
        lap!(timer, "Initialize call stack");

        // Execute the circuit.
        let response = self.get_stack(request.program_id())?.execute_function::<A, true>(call_stack)?;
        lap!(timer, "Execute the function");

        // Extract the trace.
        let trace = Arc::try_unwrap(trace).unwrap().into_inner();
        // Ensure the trace is not empty.
        ensure!(!trace.transitions().is_empty(), "Execution of '{locator}' is empty");

        finish!(timer);
        Ok((response, trace))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::types::Address;

    type CurrentNetwork = console::network::Testnet3;
    type CurrentAleo = circuit::AleoV0;

    #[test]
    fn test_execute_fee_private() {
        let rng = &mut TestRng::default();

        // Initialize the process.
        let process = Process::<CurrentNetwork>::load().unwrap();

        // Sample a private key.
        let private_key = PrivateKey::<CurrentNetwork>::new(rng).unwrap();
        let owner = Address::try_from(private_key).unwrap();
        // Sample a fee in microcredits.
        let fee_in_microcredits = rng.gen();
        // Sample a credits record.
        let credits = Record::<CurrentNetwork, Plaintext<_>>::from_str(&format!(
            "{{ owner: {owner}.private, microcredits: {fee_in_microcredits}u64.private, _nonce: 0group.public }}"
        ))
        .unwrap();
        // Sample a deployment or execution ID.
        let deployment_or_execution_id = Field::rand(rng);

        // Initialize the authorization.
        let authorization = process
            .authorize_fee_private(&private_key, credits, fee_in_microcredits, deployment_or_execution_id, rng)
            .unwrap();
        assert!(authorization.is_fee_private(), "Authorization must be for a call to 'credits.aleo/fee_private'");

        // Execute the authorization.
        let (response, trace) = process.execute::<CurrentAleo>(authorization).unwrap();
        // Ensure the response has 1 output.
        assert_eq!(response.outputs().len(), 1, "Execution of 'credits.aleo/fee_private' must contain 1 output");
        // Ensure the response has 1 output ID.
        assert_eq!(response.output_ids().len(), 1, "Execution of 'credits.aleo/fee_private' must contain 1 output ID");
        // Ensure the trace contains 1 transition.
        assert_eq!(trace.transitions().len(), 1, "Execution of 'credits.aleo/fee_private' must contain 1 transition");

        // Retrieve the transition.
        let transition = trace.transitions()[0].clone();
        assert!(transition.is_fee_private(), "Transition must be for 'credits.aleo/fee_private'");
    }

    #[test]
    fn test_execute_fee_public() {
        let rng = &mut TestRng::default();

        // Initialize the process.
        let process = Process::<CurrentNetwork>::load().unwrap();

        // Sample a private key.
        let private_key = PrivateKey::new(rng).unwrap();
        // Sample a fee in microcredits.
        let fee_in_microcredits = rng.gen();
        // Sample a deployment or execution ID.
        let deployment_or_execution_id = Field::rand(rng);

        // Compute the authorization.
        let authorization =
            process.authorize_fee_public(&private_key, fee_in_microcredits, deployment_or_execution_id, rng).unwrap();
        assert!(authorization.is_fee_public(), "Authorization must be for a call to 'credits.aleo/fee_public'");

        // Execute the authorization.
        let (response, trace) = process.execute::<CurrentAleo>(authorization).unwrap();
        // Ensure the response has 1 outputs.
        assert_eq!(response.outputs().len(), 1, "Execution of 'credits.aleo/fee_public' must contain 1 outputs");
        // Ensure the response has 1 output IDs.
        assert_eq!(response.output_ids().len(), 1, "Execution of 'credits.aleo/fee_public' must contain 0 output IDs");
        // Ensure the trace contains 1 transition.
        assert_eq!(trace.transitions().len(), 1, "Execution of 'credits.aleo/fee_public' must contain 1 transition");

        // Retrieve the transition.
        let transition = trace.transitions()[0].clone();
        assert!(transition.is_fee_public(), "Transition must be for 'credits.aleo/fee_public'");
    }
}
