//! Well-known qualifiers for use with [`super::Qualifiers::get_typed`] and
//! [`super::Qualifiers::insert_typed`].

use std::borrow::Cow;
use std::collections::HashMap;

use hex::{FromHex, ToHex};

use crate::{copy_as_lowercase, ParseError, SmallString};

pub mod gem;
pub mod maven;

/// A type that has an associated qualifier key.
pub trait KnownQualifierKey {
    /// The key of the qualifier.
    ///
    /// This must be a valid qualifier key or attempting to set the qualifier
    /// will panic.
    const KEY: &'static str;
}

macro_rules! str_ref_qualifier {
    ($type_name:ident, $qualifier_key:literal, $human_name:literal) => {
        #[doc = concat!("A ", $human_name, " qualifier.")]
        pub struct $type_name<'a>(&'a str);

        impl<'a> AsRef<str> for $type_name<'a> {
            fn as_ref(&self) -> &str {
                self.0
            }
        }

        impl<'a> From<$type_name<'a>> for &'a str {
            fn from(value: $type_name<'a>) -> Self {
                value.0
            }
        }

        impl<'a> From<&'a str> for $type_name<'a> {
            fn from(value: &'a str) -> Self {
                $type_name(value)
            }
        }

        impl<'a> From<$type_name<'a>> for $crate::SmallString {
            fn from(value: $type_name<'a>) -> Self {
                Self::from(<&'a str>::from(value))
            }
        }

        impl<'a> ::std::ops::Deref for $type_name<'a> {
            type Target = str;

            fn deref(&self) -> &str {
                self.0
            }
        }

        impl<'a> $crate::qualifiers::well_known::KnownQualifierKey for $type_name<'a> {
            const KEY: &'static str = $qualifier_key;
        }
    };
}
// Allow child modules to use this macro.
use str_ref_qualifier;

str_ref_qualifier!(RepositoryUrl, "repository_url", "repository URL");
str_ref_qualifier!(DownloadUrl, "download_url", "download URL");
str_ref_qualifier!(VcsUrl, "vcs_url", "VCS URL");
str_ref_qualifier!(FileName, "file_name", "file name");

/// A checksum qualifier.
///
/// # Example
///
/// ```
/// use phylum_purl::qualifiers::well_known::Checksum;
/// use phylum_purl::GenericPurl;
///
/// let sha256 =
///     hex::decode("e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855").unwrap();
/// let mut checksums = Checksum::default();
/// checksums.insert("sha256", sha256);
/// let purl = GenericPurl::<String>::builder("type".to_owned(), "name")
///     .try_with_typed_qualifier(Some(checksums))
///     .unwrap()
///     .build()
///     .unwrap();
/// assert_eq!(
///     "pkg:type/name?checksum=sha256:\
///      e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
///     purl.to_string(),
/// );
/// ```
#[derive(Clone, Debug, Default)]
pub struct Checksum<'a> {
    algorithms: HashMap<SmallString, Cow<'a, str>>,
}

impl<'a> KnownQualifierKey for Checksum<'a> {
    const KEY: &'static str = "checksum";
}

impl<'a> TryFrom<&'a str> for Checksum<'a> {
    type Error = ParseError;

    fn try_from(value: &'a str) -> Result<Self, Self::Error> {
        let mut algorithms =
            HashMap::with_capacity(value.chars().filter(|c| *c == ',').count() + 1);
        for hash in value.split(',') {
            let Some((algorithm, bytes)) = hash.rsplit_once(':') else {
                return Err(ParseError::InvalidQualifier);
            };

            let algorithm = copy_as_lowercase(algorithm);

            if algorithms.insert(algorithm, Cow::Borrowed(bytes)).is_some() {
                // Duplicate algorithm.
                return Err(ParseError::InvalidQualifier);
            }
        }

        Ok(Self { algorithms })
    }
}

impl<'a> TryFrom<Checksum<'a>> for SmallString {
    type Error = ParseError;

    fn try_from(value: Checksum<'a>) -> Result<Self, Self::Error> {
        let mut algorithms: Vec<_> = value.algorithms.into_iter().collect();
        algorithms.sort_unstable_by(|a, b| a.0.cmp(&b.0));

        let mut v = String::with_capacity(
            algorithms.iter().map(|(k, v)| k.len() + 1 + v.len()).sum::<usize>() + algorithms.len()
                - 1,
        );
        for (algorithm, bytes) in algorithms {
            if bytes.chars().any(|b| !b.is_ascii_hexdigit()) || bytes.len() % 2 != 0 {
                return Err(ParseError::InvalidQualifier);
            }

            if !v.is_empty() {
                v.push(',');
            }
            v.push_str(&algorithm);
            v.push(':');
            v.extend(bytes.chars().map(|c| c.to_ascii_lowercase()));
        }
        Ok(SmallString::from(v))
    }
}

impl<'a> Checksum<'a> {
    /// Get a reference to the hex bytes of a hash.
    ///
    /// The hash may not be valid hex bytes.
    ///
    /// To decode the value into bytes, use [`Self::get`].
    pub fn get_raw<'b>(&'b self, algorithm: &str) -> Option<&'b str> {
        self.algorithms.get(algorithm).map(|v| &**v)
    }

    /// Get the value of a hash as type `T`.
    ///
    /// To get the hex bytes, use [`Self::get_raw`].
    pub fn get<T>(&self, algorithm: &str) -> Result<Option<T>, T::Error>
    where
        T: FromHex,
    {
        self.get_raw(algorithm).map(T::from_hex).transpose()
    }

    /// Get an iterator over all the algorithm names.
    pub fn algorithms(&self) -> impl Iterator<Item = &str> {
        self.algorithms.keys().map(|k| &**k)
    }

    /// Set the hex bytes of a hash.
    ///
    /// The hex bytes are not validated.
    ///
    /// If the value is not already hex-encoded, use `[Self::insert]`.
    pub fn insert_raw(&mut self, algorithm: &str, value: String) {
        if let Some(v) = self.algorithms.get_mut(algorithm) {
            *v = Cow::Owned(value);
        } else {
            self.algorithms.insert(copy_as_lowercase(algorithm), Cow::Owned(value));
        }
    }

    /// Set the value of a hash.
    ///
    /// The value will be hex encoded. If the value is already a hex string, use
    /// [`Self::insert_raw`].
    pub fn insert<T>(&mut self, algorithm: &str, value: T)
    where
        T: ToHex,
    {
        self.insert_raw(algorithm, value.encode_hex())
    }

    /// Remove a hash.
    pub fn remove(&mut self, algorithm: &str) {
        self.algorithms.remove(algorithm);
    }
}

#[cfg(test)]
mod tests {
    use std::borrow::Cow;

    use super::*;
    use crate::{GenericPurl, Qualifiers};

    #[test]
    fn can_get_repository_url() {
        const URL: &str = "docker.io/library/debian";
        let purl = GenericPurl::builder(Cow::Borrowed("oci"), "debian")
            .with_qualifier("repository_url", URL)
            .unwrap()
            .build()
            .unwrap();
        assert_eq!(Some(URL), purl.qualifiers().get_typed::<RepositoryUrl>().as_deref())
    }

    #[test]
    fn can_set_repository_url() {
        const URL: &str = "ghcr.io/debian";
        let purl = GenericPurl::builder(Cow::Borrowed("oci"), "debian")
            .with_typed_qualifier(Some(RepositoryUrl::from(URL)))
            .build()
            .unwrap();
        assert_eq!(Some(URL), purl.qualifiers().get("repository_url"))
    }

    #[test]
    fn can_remove_repository_url() {
        let mut qualifiers =
            Qualifiers::try_from_iter([("repository_url", "gcr.io/distroless")]).unwrap();
        assert!(qualifiers.contains_typed::<RepositoryUrl>());
        qualifiers.remove_typed::<RepositoryUrl>();
        assert!(!qualifiers.contains_typed::<RepositoryUrl>());
    }

    mod checksum {
        use std::fmt::Write;

        use hex::FromHexError;
        use maplit::hashmap;

        use super::*;

        #[test]
        fn get_raw_gets_when_set_gets_whatever_value() {
            let checksums = Checksum {
                algorithms: hashmap! {
                    SmallString::from("hash1") => Cow::Borrowed("x"),
                },
            };
            assert_eq!(Some("x"), checksums.get_raw("hash1"));
        }

        #[test]
        fn get_raw_gets_when_unset_returns_none() {
            let checksums = Checksum::default();
            assert_eq!(None, checksums.get_raw("hash1"));
        }

        #[test]
        fn get_when_set_and_valid_returns_value() {
            let checksums = Checksum {
                algorithms: hashmap! {
                    SmallString::from("hash1") => Cow::Borrowed("000102"),
                },
            };
            assert_eq!(
                Some([0u8, 1, 2].as_slice()),
                checksums.get::<Vec<u8>>("hash1").unwrap().as_deref(),
            );
        }

        #[test]
        fn get_when_set_and_invalid_returns_error() {
            let checksums = Checksum {
                algorithms: hashmap! {
                    SmallString::from("hash1") => Cow::Borrowed("xx"),
                },
            };
            let error = checksums.get::<Vec<u8>>("hash1").unwrap_err();
            assert_eq!(FromHexError::InvalidHexCharacter { c: 'x', index: 0 }, error);
        }

        #[test]
        fn get_when_unset_returns_none() {
            let checksums = Checksum::default();
            assert_eq!(None, checksums.get::<Vec<u8>>("hash1").unwrap().as_deref());
        }

        #[test]
        fn algorithms_returns_algorithms() {
            let checksums = Checksum {
                algorithms: hashmap! {
                    SmallString::from("hash1") => Cow::Borrowed("xx"),
                },
            };
            let algorithms: Vec<_> = checksums.algorithms().collect();
            assert_eq!(&["hash1"], &algorithms[..]);
        }

        #[test]
        fn insert_raw_when_already_set_replaces() {
            let mut checksums = Checksum {
                algorithms: hashmap! {
                    SmallString::from("hash1") => Cow::Borrowed("xx"),
                },
            };
            checksums.insert_raw("hash1", "yy".to_owned());
            assert_eq!(Some("yy"), checksums.get_raw("hash1"));
        }

        #[test]
        fn insert_raw_when_already_set_with_different_case_replaces() {
            let mut checksums = Checksum {
                algorithms: hashmap! {
                    SmallString::from("hash1") => Cow::Borrowed("xx"),
                },
            };
            checksums.insert_raw("HASH1", "yy".to_owned());
            assert_eq!(Some("yy"), checksums.get_raw("hash1"));
        }

        #[test]
        fn insert_raw_when_not_set_inserts() {
            let mut checksums = Checksum::default();
            checksums.insert_raw("hash1", "yy".to_owned());
            assert_eq!(Some("yy"), checksums.get_raw("hash1"));
        }

        #[test]
        fn insert_raw_lowercases_algorithm() {
            let mut checksums = Checksum::default();
            checksums.insert_raw("HASH1", "yy".to_owned());
            assert_eq!(Some("yy"), checksums.get_raw("hash1"));
        }

        #[test]
        fn insert_inserts_encoded() {
            let mut checksums = Checksum::default();
            checksums.insert("hash1", "\x00\x01\x02");
            assert_eq!(Some("000102"), checksums.get_raw("hash1"));
        }

        #[test]
        fn remove_removes() {
            let mut checksums = Checksum {
                algorithms: hashmap! {
                    SmallString::from("hash1") => Cow::Borrowed("xx"),
                },
            };
            checksums.remove("hash1");
            assert_eq!(None, checksums.get_raw("hash1"));
        }

        #[test]
        fn try_from_str_when_valid_parses() {
            // This is valid enough for parsing.
            let checksums = Checksum::try_from("HASH1:0,hash0:x").unwrap();
            assert_eq!(Some("0"), checksums.get_raw("hash1"));
            assert_eq!(Some("x"), checksums.get_raw("hash0"));
        }

        #[test]
        fn try_from_str_when_invalid_returns_error() {
            let error = Checksum::try_from(",").unwrap_err();
            assert!(matches!(error, ParseError::InvalidQualifier));
        }

        #[test]
        fn try_from_str_when_algorithm_is_duplicated_returns_error() {
            let error = Checksum::try_from("hash1:00,hash1:00").unwrap_err();
            assert!(matches!(error, ParseError::InvalidQualifier));
        }

        #[test]
        fn try_into_str_when_non_hex_returns_error() {
            let checksums = Checksum {
                algorithms: hashmap! {
                    SmallString::from("hash1") => Cow::Borrowed("xx"),
                },
            };
            let error = SmallString::try_from(checksums).unwrap_err();
            assert!(matches!(error, ParseError::InvalidQualifier));
        }

        #[test]
        fn try_into_str_when_partial_byte_returns_error() {
            let checksums = Checksum {
                algorithms: hashmap! {
                    SmallString::from("hash1") => Cow::Borrowed("0"),
                },
            };
            let error = SmallString::try_from(checksums).unwrap_err();
            assert!(matches!(error, ParseError::InvalidQualifier));
        }

        #[test]
        fn try_into_str_returns_algorithms_in_order_with_lowercase_hex_bytes() {
            let mut expected = SmallString::default();
            for i in 0..10 {
                if !expected.is_empty() {
                    expected.push(',');
                }
                write!(expected, "hash{i}:{i:02x}").unwrap();
            }

            let mut checksums = Checksum::default();
            for i in (0..10u8).rev() {
                checksums.insert(&format!("HASH{i}"), [i]);
            }
            let actual = SmallString::try_from(checksums).unwrap();

            assert_eq!(expected, actual);
        }
    }
}
