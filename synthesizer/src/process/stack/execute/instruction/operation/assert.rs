// Copyright (C) 2019-2023 Aleo Systems Inc.
// This file is part of the snarkVM library.

// The snarkVM library is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// The snarkVM library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with the snarkVM library. If not, see <https://www.gnu.org/licenses/>.

use super::*;

impl<N: Network, const VARIANT: u8> Stack<N> {
    /// Executes the instruction.
    #[inline]
    pub fn execute<A: circuit::Aleo<Network = N>>(
        &self,
        assert: &AssertInstruction<N, VARIANT>,
        registers: &mut Registers<N, A>,
    ) -> Result<()> {
        // Ensure the number of operands is correct.
        if assert.operands().len() != 2 {
            bail!(
                "Instruction '{}' expects 2 operands, found {} operands",
                AssertInstruction::opcode(),
                assert.operands().len()
            )
        }

        // Retrieve the inputs.
        let input_a = registers.load_circuit(&self, &assert.operands()[0])?;
        let input_b = registers.load_circuit(&self, &assert.operands()[1])?;

        // Assert the inputs.
        match VARIANT {
            0 => A::assert(input_a.is_equal(&input_b)),
            1 => A::assert(input_a.is_not_equal(&input_b)),
            _ => bail!("Invalid 'assert' variant: {VARIANT}"),
        }
        Ok(())
    }
}