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

static PUZZLE_COMMITMENT_PREFIX: &str = "puzzle";

impl<N: Network> FromStr for PuzzleCommitment<N> {
    type Err = Error;

    /// Reads in the puzzle commitment string.
    fn from_str(puzzle_commitment: &str) -> Result<Self, Self::Err> {
        // Decode the puzzle commitment string from bech32m.
        let (hrp, data, variant) = bech32::decode(puzzle_commitment)?;
        if hrp != PUZZLE_COMMITMENT_PREFIX {
            bail!("Failed to decode puzzle commitment: '{hrp}' is an invalid prefix")
        } else if data.is_empty() {
            bail!("Failed to decode puzzle commitment: data field is empty")
        } else if variant != bech32::Variant::Bech32m {
            bail!("Found a puzzle commitment that is not bech32m encoded: {puzzle_commitment}");
        }
        // Decode the puzzle commitment data from u5 to u8, and into the puzzle commitment.
        Ok(Self::read_le(&Vec::from_base32(&data)?[..])?)
    }
}

impl<N: Network> Debug for PuzzleCommitment<N> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

impl<N: Network> Display for PuzzleCommitment<N> {
    /// Writes the puzzle commitment as a bech32m string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        // Convert the puzzle commitment to bytes.
        let bytes = self.to_bytes_le().map_err(|_| fmt::Error)?;
        // Encode the bytes into bech32m.
        let string = bech32::encode(PUZZLE_COMMITMENT_PREFIX, bytes.to_base32(), bech32::Variant::Bech32m)
            .map_err(|_| fmt::Error)?;
        // Output the string.
        Display::fmt(&string, f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::network::Testnet3;

    type CurrentNetwork = Testnet3;

    const ITERATIONS: u64 = 1_000;

    #[test]
    fn test_string() -> Result<()> {
        // Ensure type and empty value fails.
        assert!(PuzzleCommitment::<CurrentNetwork>::from_str(&format!("{PUZZLE_COMMITMENT_PREFIX}1")).is_err());
        assert!(PuzzleCommitment::<CurrentNetwork>::from_str("").is_err());

        let mut rng = TestRng::default();

        for _ in 0..ITERATIONS {
            // Sample a new puzzle commitment.
            let expected = PuzzleCommitment::<CurrentNetwork>::new(KZGCommitment(rng.gen()));

            // Check the string representation.
            let candidate = format!("{expected}");
            assert_eq!(expected, PuzzleCommitment::from_str(&candidate)?);
            assert_eq!(PUZZLE_COMMITMENT_PREFIX, candidate.to_string().split('1').next().unwrap());
        }
        Ok(())
    }

    #[test]
    fn test_display() -> Result<()> {
        let mut rng = TestRng::default();

        for _ in 0..ITERATIONS {
            // Sample a new puzzle commitment.
            let expected = PuzzleCommitment::<CurrentNetwork>::new(KZGCommitment(rng.gen()));

            let candidate = expected.to_string();
            assert_eq!(format!("{expected}"), candidate);
            assert_eq!(PUZZLE_COMMITMENT_PREFIX, candidate.split('1').next().unwrap());

            let candidate_recovered = PuzzleCommitment::<CurrentNetwork>::from_str(&candidate.to_string())?;
            assert_eq!(expected, candidate_recovered);
        }
        Ok(())
    }
}
