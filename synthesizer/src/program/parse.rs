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

impl<N: Network> Parser for Program<N> {
    /// Parses a string into a program.
    #[inline]
    fn parse(string: &str) -> ParserResult<Self> {
        // A helper to parse a program.
        enum P<N: Network> {
            M(Mapping<N>),
            I(Struct<N>),
            R(RecordType<N>),
            C(Closure<N>),
            F(Function<N>),
        }

        // Parse the imports from the string.
        let (string, imports) = many0(Import::parse)(string)?;
        // Parse the whitespace and comments from the string.
        let (string, _) = Sanitizer::parse(string)?;
        // Parse the 'program' keyword from the string.
        let (string, _) = tag(Self::type_name())(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the program ID from the string.
        let (string, id) = ProgramID::parse(string)?;
        // Parse the whitespace from the string.
        let (string, _) = Sanitizer::parse_whitespaces(string)?;
        // Parse the semicolon ';' keyword from the string.
        let (string, _) = tag(";")(string)?;

        // Parse the struct or function from the string.
        let (string, components) = many1(alt((
            map(Mapping::parse, |mapping| P::<N>::M(mapping)),
            map(Struct::parse, |struct_| P::<N>::I(struct_)),
            map(RecordType::parse, |record| P::<N>::R(record)),
            map(Closure::parse, |closure| P::<N>::C(closure)),
            map(Function::parse, |function| P::<N>::F(function)),
        )))(string)?;
        // Parse the whitespace and comments from the string.
        let (string, _) = Sanitizer::parse(string)?;

        // Return the program.
        map_res(take(0usize), move |_| {
            // Initialize a new program.
            let mut program = match Program::<N>::new(id) {
                Ok(program) => program,
                Err(error) => {
                    eprintln!("{error}");
                    return Err(error);
                }
            };
            // Construct the program with the parsed components.
            for component in components.iter() {
                let result = match component {
                    P::M(mapping) => program.add_mapping(mapping.clone()),
                    P::I(struct_) => program.add_struct(struct_.clone()),
                    P::R(record) => program.add_record(record.clone()),
                    P::C(closure) => program.add_closure(closure.clone()),
                    P::F(function) => program.add_function(function.clone()),
                };

                match result {
                    Ok(_) => (),
                    Err(error) => {
                        eprintln!("{error}");
                        return Err(error);
                    }
                }
            }
            // Lastly, add the imports (if any) to the program.
            for import in imports.iter() {
                match program.add_import(import.clone()) {
                    Ok(_) => (),
                    Err(error) => {
                        eprintln!("{error}");
                        return Err(error);
                    }
                }
            }
            // Output the program.
            Ok::<_, Error>(program)
        })(string)
    }
}

impl<N: Network> FromStr for Program<N> {
    type Err = Error;

    /// Returns a program from a string literal.
    fn from_str(string: &str) -> Result<Self> {
        match Self::parse(string) {
            Ok((remainder, object)) => {
                // Ensure the remainder is empty.
                ensure!(remainder.is_empty(), "Failed to parse string. Remaining invalid string is: \"{remainder}\"");
                // Return the object.
                Ok(object)
            }
            Err(error) => bail!("Failed to parse string. {error}"),
        }
    }
}

impl<N: Network> Debug for Program<N> {
    /// Prints the program as a string.
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Display::fmt(self, f)
    }
}

#[allow(clippy::format_push_string)]
impl<N: Network> Display for Program<N> {
    /// Prints the program as a string.
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        // Initialize a string for the program.
        let mut program = String::new();

        if !self.imports.is_empty() {
            // Print the imports.
            for import in self.imports.values() {
                program.push_str(&format!("{import}\n"));
            }

            // Print a newline.
            program.push('\n');
        }

        // Print the program name.
        program += &format!("{} {};\n\n", Self::type_name(), self.id);

        for (identifier, definition) in self.identifiers.iter() {
            match definition {
                ProgramDefinition::Mapping => match self.mappings.get(identifier) {
                    Some(mapping) => program.push_str(&format!("{mapping}\n\n")),
                    None => {
                        eprintln!("Mapping '{identifier}' is not defined.");
                        return Err(fmt::Error);
                    }
                },
                ProgramDefinition::Struct => match self.structs.get(identifier) {
                    Some(struct_) => program.push_str(&format!("{struct_}\n\n")),
                    None => {
                        eprintln!("Struct '{identifier}' is not defined.");
                        return Err(fmt::Error);
                    }
                },
                ProgramDefinition::Record => match self.records.get(identifier) {
                    Some(record) => program.push_str(&format!("{record}\n\n")),
                    None => {
                        eprintln!("Record '{identifier}' is not defined.");
                        return Err(fmt::Error);
                    }
                },
                ProgramDefinition::Closure => match self.closures.get(identifier) {
                    Some(closure) => program.push_str(&format!("{closure}\n\n")),
                    None => {
                        eprintln!("Closure '{identifier}' is not defined.");
                        return Err(fmt::Error);
                    }
                },
                ProgramDefinition::Function => match self.functions.get(identifier) {
                    Some(function) => program.push_str(&format!("{function}\n\n")),
                    None => {
                        eprintln!("Function '{identifier}' is not defined.");
                        return Err(fmt::Error);
                    }
                },
            }
        }
        // Remove the last newline.
        program.pop();

        write!(f, "{program}")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use console::network::Testnet3;

    type CurrentNetwork = Testnet3;

    #[test]
    fn test_program_parse() -> Result<()> {
        // Initialize a new program.
        let (string, program) = Program::<CurrentNetwork>::parse(
            r"
program to_parse.aleo;

struct message:
    first as field;
    second as field;

function compute:
    input r0 as message.private;
    add r0.first r0.second into r1;
    output r1 as field.private;",
        )
        .unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");

        // Ensure the program contains the struct.
        assert!(program.contains_struct(&Identifier::from_str("message")?));
        // Ensure the program contains the function.
        assert!(program.contains_function(&Identifier::from_str("compute")?));

        Ok(())
    }

    #[test]
    fn test_program_parse_function_zero_inputs() -> Result<()> {
        // Initialize a new program.
        let (string, program) = Program::<CurrentNetwork>::parse(
            r"
program to_parse.aleo;

function compute:
    add 1u32 2u32 into r0;
    output r0 as u32.private;",
        )
        .unwrap();
        assert!(string.is_empty(), "Parser did not consume all of the string: '{string}'");

        // Ensure the program contains the function.
        assert!(program.contains_function(&Identifier::from_str("compute")?));

        Ok(())
    }

    #[test]
    fn test_program_display() -> Result<()> {
        let expected = r"program to_parse.aleo;

struct message:
    first as field;
    second as field;

function compute:
    input r0 as message.private;
    add r0.first r0.second into r1;
    output r1 as field.private;
";
        // Parse a new program.
        let program = Program::<CurrentNetwork>::from_str(expected)?;
        // Ensure the program string matches.
        assert_eq!(expected, format!("{program}"));

        Ok(())
    }

    #[test]
    fn test_program_containing_maximum_number_of_mappings() {
        // Initialize a new program string.
        let mut program_string = "program test.aleo;".to_string();
        // Add one more than the maximum number of mappings.
        for i in 0..<CurrentNetwork as Network>::MAX_MAPPINGS {
            program_string
                .push_str(&format!("mapping map_{}:key left as field.public;value right as field.public;", i));
        }
        // Add a dummy function.
        program_string.push_str("function foo:");
        // Attempt to parse the program.
        let result = Program::<CurrentNetwork>::from_str(&program_string);
        // Ensure the program failed to parse.
        assert!(result.is_ok());
    }

    #[test]
    fn test_program_exceeding_maximum_number_of_mappings() {
        // Initialize a new program string.
        let mut program_string = "program test.aleo;".to_string();
        // Add one more than the maximum number of mappings.
        for i in 0..=<CurrentNetwork as Network>::MAX_MAPPINGS {
            program_string
                .push_str(&format!("mapping map_{}:key left as field.public;value right as field.public;", i));
        }
        // Add a dummy function.
        program_string.push_str("function foo:");
        // Attempt to parse the program.
        let result = Program::<CurrentNetwork>::from_str(&program_string);
        // Ensure the program failed to parse.
        assert!(result.is_err());
    }
}
