#![doc = include_str!("../README.md")]
#![cfg_attr(docsrs, feature(doc_auto_cfg))]

use std::borrow::Cow;

pub use builder::*;
pub use format::*;
#[cfg(feature = "package-type")]
pub use package_type::*;
pub use parse::*;
pub use qualifiers::Qualifiers;
use smartstring::{LazyCompact, SmartString, SmartStringMode};

mod builder;
mod format;
#[cfg(feature = "package-type")]
mod package_type;
mod parse;
pub mod qualifiers;

/// A string that may be stored inline instead of on the heap.
///
/// PURLs may contain many small strings so this saves on heap allocations.
// This needs to be public because it gets exposed in some methods of Qualifiers.
#[cfg(feature = "smartstring")]
pub type SmallString = SmartString<LazyCompact>;
// When compiling without smartstring we'll just use regular Strings.
#[cfg(not(feature = "smartstring"))]
type SmallString = String;

/// A type that provides package-type-specific behavior.
///
/// If it supports your requirements, you can use or extend [`PackageType`].
/// (see also [`Purl`])
///
/// If you don't care about package-type-specific behavior, you can use
/// [`String`], [`Cow<str>`], or [`SmallString`].
///
/// # Example
///
/// ```
/// use std::borrow::Cow;
/// use std::str::FromStr;
///
/// use phylum_purl::{GenericPurl, GenericPurlBuilder, ParseError, PurlParts, PurlShape};
///
/// enum MyPackageType {
///     Custom,
/// }
///
/// #[derive(Debug, thiserror::Error)]
/// enum MyError {
///     #[error("Parse error: {0}")]
///     Parse(#[from] ParseError),
///     #[error("Unsupported package type")]
///     UnsupportedType,
///     #[error("Required repository_url qualifier was not found")]
///     MissingRepositoryUrl,
/// }
///
/// impl FromStr for MyPackageType {
///     type Err = MyError;
///
///     fn from_str(s: &str) -> Result<Self, Self::Err> {
///         if s.eq_ignore_ascii_case("custom") {
///             Ok(MyPackageType::Custom)
///         } else {
///             Err(MyError::UnsupportedType)
///         }
///     }
/// }
///
/// impl PurlShape for MyPackageType {
///     type Error = MyError;
///
///     fn package_type(&self) -> Cow<str> {
///         match self {
///             // Always use lower case types here.
///             // Upper case characters are not invalid, but the canonical type name is always
///             // lower case.
///             MyPackageType::Custom => Cow::Borrowed("custom"),
///         }
///     }
///
///     fn finish(&mut self, parts: &mut PurlParts) -> Result<(), Self::Error> {
///         match self {
///             MyPackageType::Custom => {
///                 // pkg:custom names are always lower case.
///                 parts.name = parts.name.to_lowercase().into();
///                 // pkg:custom requires a repository_url.
///                 if !parts.qualifiers.contains_key("repository_url") {
///                     return Err(MyError::MissingRepositoryUrl);
///                 }
///             },
///         }
///         Ok(())
///     }
/// }
///
/// type Purl = GenericPurl<MyPackageType>;
/// type PurlBuilder = GenericPurlBuilder<MyPackageType>;
///
/// assert!(matches!(
///     Purl::from_str("pkg:custom/Example?repository_url=https://example.com/")
///         .map(|p| p.to_string())
///         .as_deref(),
///     Ok("pkg:custom/example?repository_url=https://example.com/"),
/// ));
/// assert!(matches!(Purl::from_str("pkg:custom/Example"), Err(MyError::MissingRepositoryUrl),));
/// ```
pub trait PurlShape {
    /// The type of error returned by this package type.
    type Error: From<ParseError>;

    /// Get the string representation of this `PurlShape`.
    ///
    /// The returned value should be a lower case string. If the returned value
    /// contains invalid characters, `Display` and `to_string` will panic.
    #[must_use]
    fn package_type(&self) -> Cow<str>;

    /// Preview and potentially modify the parts that make up a PURL.
    ///
    /// This is called when a [`GenericPurl`] is being created. It gives the
    /// `PurlShape` implementation a chance to perform validation and
    /// normalization.
    fn finish(&mut self, parts: &mut PurlParts) -> Result<(), Self::Error>;
}

/// A generic [`PurlShape`] that can support any package type but does not
/// provide any type-specific functionality.
///
/// Without type-specific functionality, it's possible to create PURLs that have
/// incorrect capitalization or are missing a required namespace or required
/// qualifiers.
impl PurlShape for String {
    type Error = ParseError;

    fn package_type(&self) -> Cow<str> {
        Cow::Borrowed(self)
    }

    fn finish(&mut self, _parts: &mut PurlParts) -> Result<(), Self::Error> {
        str_preview_mut(self)?;
        Ok(())
    }
}

/// A generic [`PurlShape`] that can support any package type but does not
/// provide any type-specific functionality.
///
/// Without type-specific functionality, it's possible to create PURLs that have
/// incorrect capitalization or are missing a required namespace or required
/// qualifiers.
impl<'a> PurlShape for Cow<'a, str> {
    type Error = ParseError;

    fn package_type(&self) -> Cow<str> {
        Cow::Borrowed(self)
    }

    fn finish(&mut self, _parts: &mut PurlParts) -> Result<(), Self::Error> {
        match self {
            Cow::Owned(v) => str_preview_mut(v)?,
            Cow::Borrowed(v) => {
                if !is_valid_package_type(v) {
                    return Err(ParseError::InvalidPackageType);
                }
                if !v.chars().all(|c| c.is_ascii_lowercase()) {
                    *self = Cow::Owned(v.to_ascii_lowercase())
                }
            },
        }
        Ok(())
    }
}

/// A generic [`PurlShape`] that can support any package type but does not
/// provide any type-specific functionality.
///
/// Without type-specific functionality, it's possible to create PURLs that have
/// incorrect capitalization or are missing a required namespace or required
/// qualifiers.
impl<M> PurlShape for SmartString<M>
where
    M: SmartStringMode,
{
    type Error = ParseError;

    fn package_type(&self) -> Cow<str> {
        Cow::Borrowed(self)
    }

    fn finish(&mut self, _parts: &mut PurlParts) -> Result<(), Self::Error> {
        str_preview_mut(self)?;
        Ok(())
    }
}

fn str_preview_mut(s: &mut str) -> Result<(), ParseError> {
    if !is_valid_package_type(s) {
        return Err(ParseError::InvalidPackageType);
    }
    s.make_ascii_lowercase();
    Ok(())
}

/// The parts that make up a PURL, minus the package type.
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq, PartialOrd, Ord)]
#[must_use]
pub struct PurlParts {
    /// The namespace.
    pub namespace: Option<SmallString>,
    /// The name.
    pub name: SmallString,
    /// The version.
    pub version: Option<SmallString>,
    /// The qualifiers.
    pub qualifiers: Qualifiers,
    /// The subpath.
    pub subpath: Option<SmallString>,
}

/// An immutable PURL.
///
/// This type does not directly include any package-type specific behavior.
///
/// # Example
///
/// ```
/// // `Purl` is an alias for `GenericPurl<PackageType>`.
/// use phylum_purl::{PackageType, Purl};
///
/// // Use the builder if you want to set fields besides the type and name.
/// let purl =
///     Purl::builder(PackageType::Npm, "my-package").with_version(Some("1.2.3")).build().unwrap();
///
/// assert_eq!("pkg:npm/my-package@1.2.3", &purl.to_string());
/// ```
///
/// # See also
///
/// See [`Purl`] for information about using the built-in [`PackageType`] enum.
///
/// See [`PurlShape`] if you want to use your own package types.
#[derive(Clone, Debug, Eq, Hash, PartialEq, PartialOrd, Ord)]
#[must_use]
pub struct GenericPurl<T> {
    package_type: T,
    parts: PurlParts,
}

impl<T> GenericPurl<T> {
    /// Create a new [`PurlBuilder`].
    pub fn builder<S>(package_type: T, name: S) -> GenericPurlBuilder<T>
    where
        SmallString: From<S>,
        T: PurlShape,
    {
        GenericPurlBuilder::new(package_type, name)
    }

    /// Create a new PURL.
    ///
    /// An error will be returned if the [`PurlShape`] implementation `T`
    /// requires additional fields to be specified for `package_type`. For
    /// example, `Purl::new(PackageType::Maven, "my-package")` will fail because
    /// Maven requires a namespace. In that case, you must use [`Self::builder`]
    /// to set the additional required fields.
    pub fn new<S>(package_type: T, name: S) -> Result<Self, T::Error>
    where
        SmallString: From<S>,
        T: PurlShape,
    {
        Self::builder(package_type, name).build()
    }

    /// Get the package type.
    #[must_use]
    pub fn package_type(&self) -> &T {
        &self.package_type
    }

    /// Get the namespace.
    #[must_use]
    pub fn namespace(&self) -> Option<&str> {
        self.parts.namespace.as_deref()
    }

    /// Get the name.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.parts.name
    }

    /// Get the version.
    #[must_use]
    pub fn version(&self) -> Option<&str> {
        self.parts.version.as_deref()
    }

    /// Get the qualifiers.
    #[must_use]
    pub fn qualifiers(&self) -> &Qualifiers {
        &self.parts.qualifiers
    }

    /// Get the subpath.
    #[must_use]
    pub fn subpath(&self) -> Option<&str> {
        self.parts.subpath.as_deref()
    }

    /// Convert this PURL into a mutable form.
    pub fn into_builder(self) -> GenericPurlBuilder<T> {
        let GenericPurl { package_type, parts } = self;
        GenericPurlBuilder { package_type, parts }
    }
}

/// Check whether a package type string is valid according to the rules of the
/// PURL spec.
#[must_use]
fn is_valid_package_type(package_type: &str) -> bool {
    package_type.chars().all(|c| c.is_ascii_alphanumeric() || ['.', '+', '-'].contains(&c))
}

/// Try to convert a `SmallString` to lowercase without allocating.
fn lowercase_in_place(s: &mut SmallString) {
    enum State {
        Lower,
        MixedAscii,
        MixedUnicode,
    }
    let mut state = State::Lower;
    for c in s.chars() {
        if c.is_uppercase() {
            if c.is_ascii() {
                state = State::MixedAscii;
            } else {
                state = State::MixedUnicode;
                break;
            }
        }
    }
    match state {
        State::Lower => {},
        State::MixedAscii => {
            s.make_ascii_lowercase();
        },
        State::MixedUnicode => {
            *s = s.chars().flat_map(|c| c.to_lowercase()).collect();
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn string_shape_converts_to_lower() {
        let purl = GenericPurlBuilder::new("TEST".to_owned(), "name")
            .build()
            .expect("Could not build PURL");
        assert_eq!("test", purl.package_type());
        assert_eq!("pkg:test/name", &purl.to_string());
    }

    #[test]
    fn string_shape_disallows_invalid_names() {
        let error = GenericPurlBuilder::new("!".to_owned(), "name")
            .build()
            .expect_err("Build with invalid type should have failed");
        assert!(matches!(error, ParseError::InvalidPackageType), "Got unexpected error {}", error,);
    }

    #[test]
    fn cow_shape_borrowed_converts_to_lower() {
        let purl = GenericPurlBuilder::new(Cow::Borrowed("TEST"), "name")
            .build()
            .expect("Could not build PURL");
        assert_eq!("test", purl.package_type());
        assert_eq!("pkg:test/name", &purl.to_string());
    }

    #[test]
    fn cow_shape_owned_converts_to_lower() {
        let purl = GenericPurlBuilder::new(Cow::Owned("TEST".to_owned()), "name")
            .build()
            .expect("Could not build PURL");
        assert_eq!("test", purl.package_type());
        assert_eq!("pkg:test/name", &purl.to_string());
    }

    #[test]
    fn cow_shape_does_not_clone_lower() {
        let original = "test";
        let purl = GenericPurlBuilder::new(Cow::Borrowed(original), "name")
            .build()
            .expect("Could not build PURL");
        assert_eq!(original.as_ptr(), purl.package_type.as_ptr());
    }

    #[test]
    fn cow_shape_does_not_clone_owned() {
        let original = "TEST".to_owned();
        let original_ptr = original.as_ptr();
        let purl = GenericPurlBuilder::new(Cow::Owned(original), "name")
            .build()
            .expect("Could not build PURL");
        assert_eq!("test", purl.package_type());
        assert_eq!(original_ptr, purl.package_type.as_ptr());
    }

    #[test]
    fn cow_shape_disallows_invalid_names() {
        let error = GenericPurlBuilder::new(Cow::Borrowed("!"), "name")
            .build()
            .expect_err("Build with invalid type should have failed");
        assert!(matches!(error, ParseError::InvalidPackageType), "Got unexpected error {}", error,);
    }

    #[test]
    fn smallstring_shape_converts_to_lower() {
        let purl = GenericPurlBuilder::new(SmallString::from("TEST"), "name")
            .build()
            .expect("Could not build PURL");
        assert_eq!("test", purl.package_type());
        assert_eq!("pkg:test/name", &purl.to_string());
    }

    #[test]
    fn smallstring_shape_disallows_invalid_names() {
        let error = GenericPurlBuilder::new(SmallString::from("!"), "name")
            .build()
            .expect_err("Build with invalid type should have failed");
        assert!(matches!(error, ParseError::InvalidPackageType), "Got unexpected error {}", error,);
    }

    #[test]
    fn into_builder_build_produces_same_purl() {
        let original = GenericPurlBuilder::new(Cow::Borrowed("type"), "name")
            .with_namespace(Some("namespace"))
            .with_subpath(Some("subpath"))
            .with_version(Some("1.0"))
            .with_qualifier("key", Some("value"))
            .unwrap()
            .build()
            .unwrap();
        let round_trip = original.clone().into_builder().build().unwrap();
        assert_eq!(original, round_trip);
    }

    #[test]
    fn lowercase_in_place_when_lower_does_nothing() {
        let mut lower = SmallString::from("a");
        lowercase_in_place(&mut lower);
        assert_eq!("a", &lower);
    }

    #[test]
    fn lowercase_in_place_when_upper_ascii_lowercases() {
        let mut lower = SmallString::from("A");
        lowercase_in_place(&mut lower);
        assert_eq!("a", &lower);
    }

    #[test]
    fn lowercase_in_place_when_upper_unicode_lowercases() {
        let mut lower = SmallString::from("Æ");
        lowercase_in_place(&mut lower);
        assert_eq!("æ", &lower);
    }
}
