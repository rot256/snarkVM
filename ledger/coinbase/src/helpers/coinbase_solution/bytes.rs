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

impl<N: Network> FromBytes for CoinbaseSolution<N> {
    /// Reads the solutions from the buffer.
    fn read_le<R: Read>(mut reader: R) -> IoResult<Self> {
        // Read the number of solutions.
        let num_solutions: u16 = FromBytes::read_le(&mut reader)?;
        // Read the solutions.
        let mut prover_solutions = Vec::with_capacity(num_solutions as usize);
        for _ in 0..num_solutions {
            prover_solutions.push(ProverSolution::read_le(&mut reader)?);
        }
        // Return the solutions.
        Ok(Self::new(prover_solutions))
    }
}

impl<N: Network> ToBytes for CoinbaseSolution<N> {
    /// Writes the solutions to the buffer.
    fn write_le<W: Write>(&self, mut writer: W) -> IoResult<()> {
        // Write the number of solutions.
        (u16::try_from(self.solutions.len()).map_err(|e| error(e.to_string()))?).write_le(&mut writer)?;
        // Write the solutions.
        for solution in self.solutions.values() {
            solution.write_le(&mut writer)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bytes() -> Result<()> {
        let mut rng = TestRng::default();

        // Sample random solutions.
        let expected = crate::helpers::coinbase_solution::serialize::tests::sample_solutions(&mut rng);

        // Check the byte representation.
        let expected_bytes = expected.to_bytes_le()?;
        assert_eq!(expected, CoinbaseSolution::read_le(&expected_bytes[..])?);
        Ok(())
    }
}
