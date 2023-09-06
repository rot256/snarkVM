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
use snarkvm_curves::traits::{PairingCurve, PairingEngine};
use snarkvm_utilities::{
    CanonicalDeserialize,
    CanonicalSerialize,
    Compress,
    FromBytes,
    Read,
    SerializationError,
    ToBytes,
    Valid,
    Validate,
    Write,
};

use anyhow::{anyhow, bail, ensure, Result};
use std::{collections::BTreeMap, ops::Range, sync::Arc};

/// The maximum degree supported by the SRS.
const MAX_NUM_POWERS: usize = NUM_POWERS_28;

lazy_static::lazy_static! {
    static ref POWERS_OF_BETA_G_15: Vec<u8> = Degree15::load_bytes().expect("Failed to load powers of beta in universal SRS");
    static ref SHIFTED_POWERS_OF_BETA_G_15: Vec<u8> = ShiftedDegree15::load_bytes().expect("Failed to load powers of beta in universal SRS");
    static ref POWERS_OF_BETA_GAMMA_G: Vec<u8> = Gamma::load_bytes().expect("Failed to load powers of beta wrt gamma * G in universal SRS");
    static ref NEG_POWERS_OF_BETA_H: Vec<u8> = NegBeta::load_bytes().expect("Failed to load negative powers of beta in universal SRS");
    static ref BETA_H: Vec<u8> = BetaH::load_bytes().expect("Failed to load negative powers of beta in universal SRS");
}

/// A vector of powers of beta G.
#[derive(Debug, Clone)]
pub struct PowersOfG<E: PairingEngine> {
    /// The powers of beta G.
    powers_of_beta_g: PowersOfBetaG<E>,
    /// Group elements of form `{ \beta^i \gamma G }`, where `i` is from 0 to `degree`,
    /// This is used for hiding.
    powers_of_beta_times_gamma_g: Arc<BTreeMap<usize, E::G1Affine>>,
    /// Group elements of form `{ \beta^{max_degree - i} H }`, where `i`
    /// is of the form `2^k - 1` for `k` in `1` to `log_2(max_degree)`.
    negative_powers_of_beta_h: Arc<BTreeMap<usize, E::G2Affine>>,
    /// Information required to enforce degree bounds. Each pair is of the form `(degree_bound, shifting_advice)`.
    /// Each pair is in the form `(degree_bound, \beta^{max_degree - i} H),` where `H` is the generator of G2,
    /// and `i` is of the form `2^k - 1` for `k` in `1` to `log_2(max_degree)`.
    prepared_negative_powers_of_beta_h: Arc<BTreeMap<usize, <E::G2Affine as PairingCurve>::Prepared>>,
    /// beta * h
    beta_h: E::G2Affine,
}

impl<E: PairingEngine> PowersOfG<E> {
    /// Initializes the hard-coded instance of the powers.
    pub fn load() -> Result<Self> {
        let powers_of_beta_g = PowersOfBetaG::load()?;

        // Reconstruct powers of beta_times_gamma_g.
        let powers_of_beta_times_gamma_g =
            Arc::new(BTreeMap::deserialize_uncompressed_unchecked(&**POWERS_OF_BETA_GAMMA_G)?);

        // Reconstruct negative powers of beta_h.
        let negative_powers_of_beta_h: Arc<BTreeMap<usize, E::G2Affine>> =
            Arc::new(BTreeMap::deserialize_uncompressed_unchecked(&**NEG_POWERS_OF_BETA_H)?);

        // Compute the prepared negative powers of beta_h.
        let prepared_negative_powers_of_beta_h: Arc<BTreeMap<usize, <E::G2Affine as PairingCurve>::Prepared>> =
            Arc::new(negative_powers_of_beta_h.iter().map(|(d, affine)| (*d, affine.prepare())).collect());

        let beta_h = E::G2Affine::deserialize_uncompressed_unchecked(&**BETA_H)?;

        // Return the powers.
        Ok(Self {
            powers_of_beta_g,
            powers_of_beta_times_gamma_g,
            negative_powers_of_beta_h,
            prepared_negative_powers_of_beta_h,
            beta_h,
        })
    }

    /// Download the powers of beta G specified by `range`.
    pub fn download_powers_for(&mut self, range: Range<usize>) -> Result<()> {
        self.powers_of_beta_g.download_powers_for(&range)
    }

    /// Extend powers
    pub fn extend_powers(&mut self, num_powers: &Vec<Vec<u8>>) -> Result<()> {
        self.powers_of_beta_g.extend_powers(num_powers)
    }

    pub async fn download_additional_powers_async(num_powers: usize) -> Result<Vec<u8>> {
        impl_get_powers!(num_powers, load_bytes_async, await).map_err(|e| e.into())
    }

    pub async fn download_additional_shifted_powers_async(num_powers: usize) -> Result<Vec<u8>> {
        impl_get_shifted_powers!(num_powers, load_bytes_async, await).map_err(|e| e.into())
    }

    pub fn estimate_powers_for(&self, range: &Range<usize>) -> Result<(Vec<usize>, bool)> {
        self.powers_of_beta_g.estimate_powers_for(range)
    }

    /// Returns the number of contiguous powers of beta G starting from the 0-th power.
    pub fn num_powers(&self) -> usize {
        self.powers_of_beta_g.num_powers()
    }

    /// Returns the maximum possible number of contiguous powers of beta G starting from the 0-th power.
    pub fn max_num_powers(&self) -> usize {
        MAX_NUM_POWERS
    }

    /// Returns the powers of beta * gamma G.
    pub fn powers_of_beta_gamma_g(&self) -> Arc<BTreeMap<usize, E::G1Affine>> {
        self.powers_of_beta_times_gamma_g.clone()
    }

    /// Returns the `index`-th power of beta * G.
    pub fn power_of_beta_g(&mut self, index: usize) -> Result<E::G1Affine> {
        self.powers_of_beta_g.power(index)
    }

    /// Returns the powers of `beta * G` that lie within `range`.
    pub fn powers_of_beta_g(&mut self, range: Range<usize>) -> Result<&[E::G1Affine]> {
        self.powers_of_beta_g.powers(range)
    }

    pub fn negative_powers_of_beta_h(&self) -> Arc<BTreeMap<usize, E::G2Affine>> {
        self.negative_powers_of_beta_h.clone()
    }

    pub fn prepared_negative_powers_of_beta_h(&self) -> Arc<BTreeMap<usize, <E::G2Affine as PairingCurve>::Prepared>> {
        self.prepared_negative_powers_of_beta_h.clone()
    }

    pub fn beta_h(&self) -> E::G2Affine {
        self.beta_h
    }
}

impl<E: PairingEngine> CanonicalSerialize for PowersOfG<E> {
    fn serialize_with_mode<W: Write>(&self, mut writer: W, mode: Compress) -> Result<(), SerializationError> {
        self.powers_of_beta_g.serialize_with_mode(&mut writer, mode)?;
        self.powers_of_beta_times_gamma_g.serialize_with_mode(&mut writer, mode)?;
        self.negative_powers_of_beta_h.serialize_with_mode(&mut writer, mode)?;
        self.beta_h.serialize_with_mode(&mut writer, mode)?;
        Ok(())
    }

    fn serialized_size(&self, mode: Compress) -> usize {
        self.powers_of_beta_g.serialized_size(mode)
            + self.powers_of_beta_times_gamma_g.serialized_size(mode)
            + self.negative_powers_of_beta_h.serialized_size(mode)
            + self.beta_h.serialized_size(mode)
    }
}

impl<E: PairingEngine> CanonicalDeserialize for PowersOfG<E> {
    fn deserialize_with_mode<R: Read>(
        mut reader: R,
        compress: Compress,
        validate: Validate,
    ) -> Result<Self, SerializationError> {
        let powers_of_beta_g = PowersOfBetaG::deserialize_with_mode(&mut reader, compress, Validate::No)?;

        // Reconstruct powers of beta_times_gamma_g.
        let powers_of_beta_times_gamma_g =
            Arc::new(BTreeMap::deserialize_with_mode(&mut reader, compress, Validate::No)?);

        // Reconstruct negative powers of beta_h.
        let negative_powers_of_beta_h: Arc<BTreeMap<usize, E::G2Affine>> =
            Arc::new(BTreeMap::deserialize_with_mode(&mut reader, compress, Validate::No)?);

        // Compute the prepared negative powers of beta_h.
        let prepared_negative_powers_of_beta_h: Arc<BTreeMap<usize, <E::G2Affine as PairingCurve>::Prepared>> =
            Arc::new(negative_powers_of_beta_h.iter().map(|(d, affine)| (*d, affine.prepare())).collect());

        let beta_h = E::G2Affine::deserialize_with_mode(&mut reader, compress, Validate::No)?;

        let powers = Self {
            powers_of_beta_g,
            powers_of_beta_times_gamma_g,
            negative_powers_of_beta_h,
            prepared_negative_powers_of_beta_h,
            beta_h,
        };
        if let Validate::Yes = validate {
            powers.check()?;
        }
        Ok(powers)
    }
}

impl<E: PairingEngine> Valid for PowersOfG<E> {
    fn check(&self) -> Result<(), SerializationError> {
        self.powers_of_beta_g.check()?;
        self.powers_of_beta_times_gamma_g.check()?;
        self.negative_powers_of_beta_h.check()?;
        self.prepared_negative_powers_of_beta_h.check()?;
        self.beta_h.check()
    }
}

impl<E: PairingEngine> FromBytes for PowersOfG<E> {
    /// Reads the powers from the buffer.
    fn read_le<R: Read>(reader: R) -> std::io::Result<Self> {
        Self::deserialize_with_mode(reader, Compress::No, Validate::No).map_err(|e| e.into())
    }
}

impl<E: PairingEngine> ToBytes for PowersOfG<E> {
    /// Writes the powers to the buffer.
    fn write_le<W: Write>(&self, writer: W) -> std::io::Result<()> {
        self.serialize_with_mode(writer, Compress::No).map_err(|e| e.into())
    }
}

#[derive(Debug, Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct PowersOfBetaG<E: PairingEngine> {
    /// Group elements of form `[G, \beta * G, \beta^2 * G, ..., \beta^d G]`.
    powers_of_beta_g: Vec<E::G1Affine>,
    /// Group elements of form `[\beta^i * G, \beta^2 * G, ..., \beta^D G]`.
    /// where D is the maximum degree supported by the SRS.
    shifted_powers_of_beta_g: Vec<E::G1Affine>,
}

impl<E: PairingEngine> PowersOfBetaG<E> {
    /// Returns the number of contiguous powers of beta G starting from the 0-th power.
    pub fn num_powers(&self) -> usize {
        self.powers_of_beta_g.len()
    }

    /// Returns the number of contiguous shifted powers of beta G starting from the 0-th power.
    pub fn num_shifted_powers(&self) -> usize {
        self.shifted_powers_of_beta_g.len()
    }

    /// Initializes the hard-coded instance of the powers.
    fn load() -> Result<Self> {
        // Deserialize the group elements.
        let powers_of_beta_g = Vec::deserialize_uncompressed_unchecked(&**POWERS_OF_BETA_G_15)?;

        // Ensure the number of elements is correct.
        ensure!(powers_of_beta_g.len() == NUM_POWERS_15, "Incorrect number of powers in the recovered SRS");

        let shifted_powers_of_beta_g = Vec::deserialize_uncompressed_unchecked(&**SHIFTED_POWERS_OF_BETA_G_15)?;
        ensure!(shifted_powers_of_beta_g.len() == NUM_POWERS_15, "Incorrect number of powers in the recovered SRS");
        Ok(PowersOfBetaG { powers_of_beta_g, shifted_powers_of_beta_g })
    }

    /// Returns the range of powers of beta G.
    /// In detail, it returns the range of the available "normal" powers of beta G, i.e. the
    /// contiguous range of powers of beta G starting from G, and, the range of shifted_powers.
    ///
    /// For example, if the output of this function is `(0..8, 24..32)`, then `self`
    /// contains the powers
    /// * `beta^0 * G, beta^1 * G, ..., beta^7 * G`, and
    /// * `beta^24 * G, ..., beta^31 * G`.
    pub fn available_powers(&self) -> (Range<usize>, Range<usize>) {
        if !self.shifted_powers_of_beta_g.is_empty() {
            let lower_shifted_bound = MAX_NUM_POWERS - self.shifted_powers_of_beta_g.len();
            ((0..self.powers_of_beta_g.len()), (lower_shifted_bound..MAX_NUM_POWERS))
        } else {
            // We can only be in this case if have downloaded all possible powers.
            assert_eq!(self.powers_of_beta_g.len(), MAX_NUM_POWERS, "Incorrect number of powers in the recovered SRS");
            ((0..MAX_NUM_POWERS), (0..MAX_NUM_POWERS))
        }
    }

    fn contains_in_normal_powers(&self, range: &Range<usize>) -> bool {
        let (normal, _) = self.available_powers();
        normal.contains(&range.start) && (normal.end >= range.end)
    }

    fn contains_in_shifted_powers(&self, range: &Range<usize>) -> bool {
        let (_, shifted) = self.available_powers();
        shifted.contains(&range.start) && (shifted.end >= range.end)
    }

    fn contains_powers(&self, range: &Range<usize>) -> bool {
        self.contains_in_normal_powers(range) || self.contains_in_shifted_powers(range)
    }

    fn distance_from_normal_of(&self, range: &Range<usize>) -> usize {
        (range.end as isize - self.available_powers().0.end as isize).unsigned_abs()
    }

    fn distance_from_shifted_of(&self, range: &Range<usize>) -> usize {
        (range.start as isize - self.available_powers().1.start as isize).unsigned_abs()
    }

    /// Assumes that we have the requisite powers.
    fn shifted_powers(&self, range: Range<usize>) -> Result<&[E::G1Affine]> {
        ensure!(
            self.contains_in_shifted_powers(&range),
            "Requested range is not contained in the available shifted powers"
        );

        if range.start < MAX_NUM_POWERS / 2 {
            ensure!(self.shifted_powers_of_beta_g.is_empty());
            // In this case, we have downloaded all the powers, and so
            // all the powers reside in self.powers_of_beta_g.
            Ok(&self.powers_of_beta_g[range])
        } else {
            // In this case, the shifted powers still reside in self.shifted_powers_of_beta_g.
            let lower = self.shifted_powers_of_beta_g.len() - (MAX_NUM_POWERS - range.start);
            let upper = self.shifted_powers_of_beta_g.len() - (MAX_NUM_POWERS - range.end);
            Ok(&self.shifted_powers_of_beta_g[lower..upper])
        }
    }

    /// Assumes that we have the requisite powers.
    fn normal_powers(&self, range: Range<usize>) -> Result<&[E::G1Affine]> {
        ensure!(self.contains_in_normal_powers(&range), "Requested range is not contained in the available powers");
        Ok(&self.powers_of_beta_g[range])
    }

    /// Returns the power of beta times G specified by `target`.
    fn power(&mut self, target: usize) -> Result<E::G1Affine> {
        self.powers(target..(target + 1)).map(|s| s[0])
    }

    /// Slices the underlying file to return a vector of affine elements between `lower` and `upper`.
    fn powers(&mut self, range: Range<usize>) -> Result<&[E::G1Affine]> {
        if range.is_empty() {
            return Ok(&self.powers_of_beta_g[0..0]);
        }
        ensure!(range.start < range.end, "Lower power must be less than upper power");
        ensure!(range.end <= MAX_NUM_POWERS, "Upper bound must be less than the maximum number of powers");
        if !self.contains_powers(&range) {
            // We must download the powers.
            self.download_powers_for(&range)?;
        }
        match self.contains_in_normal_powers(&range) {
            true => self.normal_powers(range),
            false => self.shifted_powers(range),
        }
    }

    pub fn estimate_powers_for(&self, range: &Range<usize>) -> Result<(Vec<usize>, bool)> {
        if self.contains_in_normal_powers(range) || self.contains_in_shifted_powers(range) {
            return Ok((Vec::new(), false));
        }
        let half_max = MAX_NUM_POWERS / 2;
        if (range.start <= half_max) && (range.end > half_max) {
            // If the range contains the midpoint, then we must download all the powers.
            // (because we round up to the next power of two).
            Ok((self.get_powers_download_queue(range.end)?, false))
        } else if self.distance_from_shifted_of(range) < self.distance_from_normal_of(range) {
            // If the range is closer to the shifted powers, then we download the shifted powers.
            Ok((self.get_shifted_powers_download_queue(range.start)?, true))
        } else {
            // Otherwise, we download the normal powers.
            Ok((self.get_powers_download_queue(range.start)?, false))
        }
    }

    pub fn download_powers_for(&mut self, range: &Range<usize>) -> Result<()> {
        if self.contains_in_normal_powers(range) || self.contains_in_shifted_powers(range) {
            return Ok(());
        }
        let half_max = MAX_NUM_POWERS / 2;
        if (range.start <= half_max) && (range.end > half_max) {
            // If the range contains the midpoint, then we must download all the powers.
            // (because we round up to the next power of two).
            self.download_powers_up_to(range.end)?;
            self.shifted_powers_of_beta_g = Vec::new();
        } else if self.distance_from_shifted_of(range) < self.distance_from_normal_of(range) {
            // If the range is closer to the shifted powers, then we download the shifted powers.
            self.download_shifted_powers_from(range.start)?;
        } else {
            // Otherwise, we download the normal powers.
            self.download_powers_up_to(range.end)?;
        }
        Ok(())
    }

    /// Get needed powers for a given degree.
    fn get_powers_download_queue(&self, end: usize) -> Result<Vec<usize>> {
        // Determine the new power of two.
        let final_power_of_two =
            end.checked_next_power_of_two().ok_or_else(|| anyhow!("Requesting too many powers"))?;
        // Ensure the total number of powers is less than the maximum number of powers.
        ensure!(final_power_of_two <= MAX_NUM_POWERS, "Requesting more powers than exist in the SRS");

        // Retrieve the current power of two.
        let current_power_of_two = self
            .powers_of_beta_g
            .len()
            .checked_next_power_of_two()
            .ok_or_else(|| anyhow!("The current degree is too large"))?;

        // Initialize a vector for the powers of two to be downloaded.
        let mut download_queue = Vec::with_capacity(14);

        // Initialize the first degree to download.
        let mut accumulator = current_power_of_two * 2;
        // Determine the powers of two to download.
        while accumulator <= final_power_of_two {
            download_queue.push(accumulator);
            accumulator =
                accumulator.checked_mul(2).ok_or_else(|| anyhow!("Overflowed while requesting a larger degree"))?;
        }
        ensure!(final_power_of_two * 2 == accumulator, "Ensure the loop terminates at the right power of two");
        Ok(download_queue)
    }

    /// This method downloads the universal SRS powers up to the `next_power_of_two(target_degree)`,
    /// and updates `Self` in place with the new powers.
    fn download_powers_up_to(&mut self, end: usize) -> Result<()> {
        let final_power_of_two =
            end.checked_next_power_of_two().ok_or_else(|| anyhow!("Requesting too many powers"))?;

        // Get download queue
        let download_queue = self.get_powers_download_queue(end)?;

        // Reserve capacity for the new powers of two.
        let additional_size = final_power_of_two
            .checked_sub(self.powers_of_beta_g.len())
            .ok_or_else(|| anyhow!("final_power_of_two is smaller than existing powers"))?;
        self.powers_of_beta_g.reserve(additional_size);

        // Download the powers of two.
        for num_powers in &download_queue {
            #[cfg(debug_assertions)]
            println!("Loading {num_powers} powers");

            // Download the universal SRS powers if they're not already on disk.
            let additional_bytes = impl_get_powers!(*num_powers, load_bytes)?;

            // Deserialize the group elements.
            let additional_powers = Vec::deserialize_uncompressed_unchecked(&*additional_bytes)?;
            // Extend the powers.
            self.powers_of_beta_g.extend(&additional_powers);
        }
        ensure!(self.powers_of_beta_g.len() == final_power_of_two, "Loaded an incorrect number of powers");
        Ok(())
    }

    pub fn extend_powers(&mut self, powers: &Vec<Vec<u8>>) -> Result<()> {
        let current_length = self.powers_of_beta_g.len();
        let final_power_of_two = powers
            .last()
            .ok_or(anyhow!("No powers to extend"))?
            .len()
            .checked_next_power_of_two()
            .ok_or(anyhow!("Adding too many powers"))?;

        let powers_length = powers.iter().fold(0, |acc, x| acc + x.len());
        ensure!((powers_length + current_length) == final_power_of_two, "Incorrect number of powers to extend");

        for power in powers {
            // TODO: Check checksum
            let additional_powers = Vec::deserialize_uncompressed_unchecked(&**power)?;
            self.powers_of_beta_g.extend(&additional_powers);
        }
        ensure!(self.powers_of_beta_g.len() == final_power_of_two, "Loaded an incorrect number of powers");
        Ok(())
    }

    fn get_shifted_powers_download_queue(&self, start: usize) -> Result<Vec<usize>> {
        // Ensure the total number of powers is less than the maximum number of powers.
        ensure!(start <= MAX_NUM_POWERS, "Requesting more powers than exist in the SRS");

        // The possible powers are:
        // (2^28 - 2^15)..=(2^28)       = 2^15 powers
        // (2^28 - 2^16)..(2^28 - 2^15) = 2^15 powers
        // (2^28 - 2^17)..(2^28 - 2^16) = 2^16 powers
        // (2^28 - 2^18)..(2^28 - 2^17) = 2^17 powers
        // (2^28 - 2^19)..(2^28 - 2^18) = 2^18 powers
        // (2^28 - 2^20)..(2^28 - 2^19) = 2^19 powers
        // (2^28 - 2^21)..(2^28 - 2^20) = 2^20 powers
        // (2^28 - 2^22)..(2^28 - 2^21) = 2^21 powers
        // (2^28 - 2^23)..(2^28 - 2^22) = 2^22 powers
        // (2^28 - 2^24)..(2^28 - 2^23) = 2^23 powers
        // (2^28 - 2^25)..(2^28 - 2^24) = 2^24 powers
        // (2^28 - 2^26)..(2^28 - 2^25) = 2^25 powers
        // (2^28 - 2^27)..(2^28 - 2^26) = 2^26 powers

        // Figure out the number of powers to download, as follows:
        // Let `start := 2^28 - k`.
        // We know that `shifted_powers_of_beta_g.len() = 2^s` such that `2^s < k`.
        // That is, we have already downloaded the powers `2^28 - 2^s` up to `2^28`.
        // Then, we have to download the powers 2^s..k.next_power_of_two().
        let final_num_powers = MAX_NUM_POWERS
            .checked_sub(start)
            .ok_or_else(|| {
                anyhow!("Requesting too many powers: `start ({start}) > MAX_NUM_POWERS ({MAX_NUM_POWERS})`")
            })?
            .checked_next_power_of_two()
            .ok_or_else(|| anyhow!("Requesting too many powers"))?; // Calculated k.next_power_of_two().

        let mut download_queue = Vec::with_capacity(14);
        let mut existing_num_powers = self.shifted_powers_of_beta_g.len();
        while existing_num_powers < final_num_powers {
            existing_num_powers = existing_num_powers
                .checked_mul(2)
                .ok_or_else(|| anyhow!("Overflowed while requesting additional powers"))?;
            download_queue.push(existing_num_powers);
        }
        download_queue.reverse(); // We want to download starting from the smallest power.
        Ok(download_queue)
    }

    /// This method downloads the universal SRS powers from
    /// `start` up to `MAXIMUM_NUM_POWERS - self.shifted_powers_of_beta_g.len()`,
    /// and updates `Self` in place with the new powers.
    fn download_shifted_powers_from(&mut self, start: usize) -> Result<()> {
        let final_num_powers = MAX_NUM_POWERS
            .checked_sub(start)
            .ok_or_else(|| {
                anyhow!("Requesting too many powers: `start ({start}) > MAX_NUM_POWERS ({MAX_NUM_POWERS})`")
            })?
            .checked_next_power_of_two()
            .ok_or_else(|| anyhow!("Requesting too many powers"))?; // Calculated k.next_power_of_two().

        let download_queue = self.get_shifted_powers_download_queue(start)?;

        let mut final_powers = Vec::with_capacity(final_num_powers);
        // If the `target_degree` exceeds the current `degree`, proceed to download the new powers.
        for num_powers in &download_queue {
            #[cfg(debug_assertions)]
            println!("Loading {num_powers} shifted powers");

            // Download the universal SRS powers if they're not already on disk.
            let additional_bytes = impl_get_shifted_powers!(*num_powers, load_bytes)?;

            // Deserialize the group elements.
            let additional_powers = Vec::deserialize_uncompressed_unchecked(&*additional_bytes)?;

            if final_powers.is_empty() {
                final_powers = additional_powers;
            } else {
                final_powers.extend(additional_powers);
            }
        }
        final_powers.extend(self.shifted_powers_of_beta_g.iter());
        self.shifted_powers_of_beta_g = final_powers;

        ensure!(
            self.shifted_powers_of_beta_g.len() == final_num_powers,
            "Loaded an incorrect number of shifted powers"
        );
        Ok(())
    }
}

impl<E: PairingEngine> FromBytes for PowersOfBetaG<E> {
    /// Reads the powers from the buffer.
    fn read_le<R: Read>(reader: R) -> std::io::Result<Self> {
        Self::deserialize_with_mode(reader, Compress::No, Validate::No).map_err(|e| e.into())
    }
}

impl<E: PairingEngine> ToBytes for PowersOfBetaG<E> {
    /// Writes the powers to the buffer.
    fn write_le<W: Write>(&self, writer: W) -> std::io::Result<()> {
        self.serialize_with_mode(writer, Compress::No).map_err(|e| e.into())
    }
}
