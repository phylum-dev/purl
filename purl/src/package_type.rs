//! Support for known package types.

use std::borrow::Cow;
use std::str::FromStr;

use phf::phf_map;
use unicase::UniCase;

use crate::{
    lowercase_in_place, GenericPurl, GenericPurlBuilder, ParseError, PurlField, PurlShape,
    SmallString,
};

/// A PURL that supports the known package types.
///
/// The spec lists many types, and some of the types may not be correct or fully
/// described. Rather than implementing an exhaustive list and potentially
/// claiming to support something that is incorrectly implemented, only some
/// types are supported here. (see also [package-url/purl-spec#38])
///
/// If you need additional types or different behavior, you can provide your own
/// [`PurlShape`] implementation.
///
/// [package-url/purl-spec#38]: https://github.com/package-url/purl-spec/issues/38
///
/// # Differences compared to current PURL spec
///
/// - The PURL spec says that NuGet package names are case sensitive, but this
///   implementation converts them to lowercase. This is consistent with the
///   behavior of NuGet, which requires clients to convert package names to
///   lowercase before calling the v3 package API. ([package-url/purl-spec#226])
/// - The PURL spec's implementation of Python package name normalization is
///   incomplete. In addition to converting dashes to underscores, periods are
///   also converted to underscores, and consequitive underscores are combined
///   into single underscores. This implementation matches the Python behavior.
///   ([package-url/purl-spec#165])
/// - The PURL spec says that NPM package names are case insensitive, but this
///   implementation does not convert them to lowercase. *New* NPM packages must
///   have lowercase names, but there are already NPM packages in existance with
///   uppercase names and those packages are distinct from other packages that
///   have the same name in lowercase. ([package-url/purl-spec#136])
///
/// [package-url/purl-spec#226]: https://github.com/package-url/purl-spec/issues/226
/// [package-url/purl-spec#165]: https://github.com/package-url/purl-spec/pull/165
/// [package-url/purl-spec#136]: https://github.com/package-url/purl-spec/issues/136
///
/// # Extending `PackageType`
///
/// If you want to extend `PackageType` with support for another package type,
/// you can do so via delegation.
///
/// ```
/// use std::borrow::Cow;
/// use std::str::FromStr;
///
/// use phylum_purl::{
///     GenericPurl, GenericPurlBuilder, PackageError, PackageType, PurlParts, PurlShape,
///     UnsupportedPackageType,
/// };
///
/// #[derive(Clone, Copy)]
/// enum MyPackageType {
///     PackageType(PackageType),
///     Custom,
/// }
///
/// type Purl = GenericPurl<MyPackageType>;
///
/// impl FromStr for MyPackageType {
///     type Err = UnsupportedPackageType;
///
///     fn from_str(s: &str) -> Result<Self, Self::Err> {
///         // Always try your types first.
///         // Otherwise there may be unexpected behavioral changes if PackageType starts
///         // supporting your types.
///         if s.eq_ignore_ascii_case("custom") {
///             Ok(MyPackageType::Custom)
///         } else {
///             PackageType::from_str(s).map(MyPackageType::PackageType)
///         }
///     }
/// }
///
/// impl PurlShape for MyPackageType {
///     type Error = PackageError;
///
///     fn package_type(&self) -> Cow<str> {
///         match self {
///             MyPackageType::PackageType(t) => t.package_type(),
///             MyPackageType::Custom => Cow::Borrowed("custom"),
///         }
///     }
///
///     fn finish(&mut self, parts: &mut PurlParts) -> Result<(), Self::Error> {
///         match self {
///             MyPackageType::PackageType(t) => t.finish(parts),
///             MyPackageType::Custom => {
///                 // your logic here
///                 Ok(())
///             },
///         }
///     }
/// }
///
/// assert!(matches!(
///     Purl::from_str("pkg:custom/example").unwrap().package_type(),
///     MyPackageType::Custom,
/// ));
/// ```
pub type Purl = GenericPurl<PackageType>;

/// A PURL builder that supports the known package types.
pub type PurlBuilder = GenericPurlBuilder<PackageType>;

/// The known package types.
///
/// This is a subset of the types described in the PURL spec repository. See
/// [`Purl`] for details.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[non_exhaustive]
pub enum PackageType {
    Cargo,
    Gem,
    Golang,
    Maven,
    Npm,
    NuGet,
    PyPI,
}

static PACKAGE_TYPES: phf::Map<UniCase<&'static str>, PackageType> = phf_map! {
    UniCase::ascii("cargo") => PackageType::Cargo,
    UniCase::ascii("gem") => PackageType::Gem,
    UniCase::ascii("golang") => PackageType::Golang,
    UniCase::ascii("maven") => PackageType::Maven,
    UniCase::ascii("npm") => PackageType::Npm,
    UniCase::ascii("nuget") => PackageType::NuGet,
    UniCase::ascii("pypi") => PackageType::PyPI,
};

impl PackageType {
    /// Get the name of the package type as a `&'static str`.
    #[must_use]
    pub const fn name(&self) -> &'static str {
        match self {
            PackageType::Cargo => "cargo",
            PackageType::Gem => "gem",
            PackageType::Golang => "golang",
            PackageType::Maven => "maven",
            PackageType::Npm => "npm",
            PackageType::NuGet => "nuget",
            PackageType::PyPI => "pypi",
        }
    }
}

impl From<PackageType> for &'static str {
    fn from(value: PackageType) -> Self {
        value.name()
    }
}

impl AsRef<str> for PackageType {
    fn as_ref(&self) -> &str {
        self.name()
    }
}

/// An error that is returned when an unsupported package type is used.
#[derive(Debug, thiserror::Error)]
#[error("Unsupported package type")]
pub struct UnsupportedPackageType;

impl FromStr for PackageType {
    type Err = UnsupportedPackageType;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        PACKAGE_TYPES.get(&UniCase::new(s)).copied().ok_or(UnsupportedPackageType)
    }
}

/// An error that is returned when working with [`PackageType`].
#[derive(Debug, thiserror::Error)]
pub enum PackageError {
    /// One or more required field is missing.
    ///
    /// # Example
    ///
    /// ```
    /// use std::str::FromStr;
    ///
    /// use phylum_purl::{PackageError, Purl, PurlField};
    ///
    /// assert!(matches!(
    ///     Purl::from_str("pkg:golang/name@version"),
    ///     Err(PackageError::MissingRequiredField(PurlField::Namespace)),
    /// ));
    /// ```
    #[error("The {0} field must be present")]
    MissingRequiredField(PurlField),
    /// The PURL could not be parsed.
    #[error("{0}")]
    Parse(#[from] ParseError),
    /// The package type is unsupported.
    #[error("Unsupported package type")]
    UnsupportedType,
}

impl From<UnsupportedPackageType> for PackageError {
    fn from(_: UnsupportedPackageType) -> Self {
        PackageError::UnsupportedType
    }
}

impl PurlShape for PackageType {
    type Error = PackageError;

    fn package_type(&self) -> Cow<str> {
        self.name().into()
    }

    fn finish(&mut self, parts: &mut crate::PurlParts) -> Result<(), Self::Error> {
        match self {
            PackageType::Cargo | PackageType::Gem | PackageType::Npm => {},
            PackageType::Golang => {
                let Some(namespace) = &mut parts.namespace else { return Err(PackageError::MissingRequiredField(PurlField::Namespace)) };
                lowercase_in_place(namespace);
                lowercase_in_place(&mut parts.name);
            },
            PackageType::Maven => {
                if parts.namespace.is_none() {
                    return Err(PackageError::MissingRequiredField(PurlField::Namespace));
                }
            },
            PackageType::NuGet => {
                lowercase_in_place(&mut parts.name);
            },
            PackageType::PyPI => {
                fix_pypi_name(&mut parts.name);
            },
        }
        Ok(())
    }
}

fn fix_pypi_name(name: &mut SmallString) {
    // https://packaging.python.org/en/latest/specifications/name-normalization/#name-normalization
    // Replace runs of consecutive ".-_" characters with a single "-".
    const DASH_CHARACTERS: &[char] = &['-', '_', '.'];
    if name.contains(DASH_CHARACTERS) {
        let mut result = SmallString::new();
        let mut in_dash = false;
        for c in name.chars() {
            if DASH_CHARACTERS.contains(&c) {
                if !in_dash {
                    result.push('-');
                    in_dash = true;
                }
            } else {
                in_dash = false;
                result.extend(c.to_lowercase());
            }
        }
        *name = result;
    } else {
        lowercase_in_place(name)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn nuget_lowercases_names() {
        let purl = PurlBuilder::new(crate::PackageType::NuGet, "Newtonsoft.Json").build().unwrap();
        assert_eq!("pkg:nuget/newtonsoft.json", &purl.to_string());
    }

    #[test]
    fn pypi_lowercases_names() {
        let purl = PurlBuilder::new(crate::PackageType::PyPI, "PyTest").build().unwrap();
        assert_eq!("pkg:pypi/pytest", &purl.to_string());
    }

    #[test]
    fn fix_pypi_name_with_leading() {
        let mut name = SmallString::from("_-.-_leading");
        fix_pypi_name(&mut name);
        assert_eq!("-leading", &name);
    }

    #[test]
    fn fix_pypi_name_with_inner() {
        let mut name = SmallString::from("inner_-.-_inner");
        fix_pypi_name(&mut name);
        assert_eq!("inner-inner", &name);
    }

    #[test]
    fn fix_pypi_name_with_trailing() {
        let mut name = SmallString::from("trailing_-.-_");
        fix_pypi_name(&mut name);
        assert_eq!("trailing-", &name);
    }

    #[test]
    fn cargo_does_not_lowercase_names() {
        let purl = PurlBuilder::new(crate::PackageType::Cargo, "Inflector").build().unwrap();
        assert_eq!("pkg:cargo/Inflector", &purl.to_string());
    }

    #[test]
    fn npm_does_not_lowercase_names() {
        let purl = PurlBuilder::new(crate::PackageType::Npm, "parseUri").build().unwrap();
        assert_eq!("pkg:npm/parseUri", &purl.to_string());
    }
}
