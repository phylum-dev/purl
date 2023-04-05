use crate::{GenericPurl, ParseError, PurlParts, PurlShape, SmallString};

/// A mutable, potentially invalid PURL.
///
/// This type is used while parsing or constructing PURLs.
/// [`GenericPurlBuilder::build`] converts the builder into an immutable,
/// validated PURL.
///
/// # Example
///
/// ```
/// // `PurlBuilder` is an alias for `GenericPurlBuilder<PackageType>`.
/// use phylum_purl::{PackageType, PurlBuilder};
///
/// // Use the builder if you want to set fields besides the type and name.
/// let purl = PurlBuilder::new(PackageType::Maven, "my-package")
///     .with_namespace(Some("my.company"))
///     .build()
///     .unwrap();
///
/// assert_eq!("pkg:maven/my.company/my-package", &purl.to_string());
/// ```
#[derive(Clone, Debug, Default)]
#[must_use]
pub struct GenericPurlBuilder<T> {
    /// The package type.
    pub package_type: T,
    /// The type-specific parts that make up the PURL.
    pub parts: PurlParts,
}

impl<T> GenericPurlBuilder<T> {
    /// Initialize a new PURL builder.
    pub fn new<S>(package_type: T, name: S) -> Self
    where
        SmallString: From<S>,
    {
        Self {
            package_type,
            parts: PurlParts { name: SmallString::from(name), ..Default::default() },
        }
    }

    /// Set the package type.
    pub fn with_package_type(mut self, new: T) -> Self {
        self.package_type = new;
        self
    }

    /// Set the namespace.
    ///
    /// Passing `None` unsets the namespace.
    pub fn with_namespace<S>(mut self, new: Option<S>) -> Self
    where
        SmallString: From<S>,
    {
        self.parts.namespace = new.map(SmallString::from);
        self
    }

    /// Unset the namespace.
    ///
    /// This is the same as passing `None` to [`Self::with_namespace`].
    pub fn without_namespace(mut self) -> Self {
        self.parts.namespace = None;
        self
    }

    /// Set the name.
    pub fn with_name<S>(mut self, new: S) -> Self
    where
        SmallString: From<S>,
    {
        self.parts.name = SmallString::from(new);
        self
    }

    /// Set the version.
    ///
    /// Passing `None` unsets the version.
    pub fn with_version<S>(mut self, new: Option<S>) -> Self
    where
        SmallString: From<S>,
    {
        self.parts.version = new.map(SmallString::from);
        self
    }

    /// Unset the version.
    ///
    /// This is the same as passing `None` to [`Self::with_version`].
    pub fn without_version(mut self) -> Self {
        self.parts.version = None;
        self
    }

    /// Set a qualifier.
    ///
    /// If `v` is `None`, the qualifier will be unset.
    pub fn with_qualifier<K, V>(mut self, k: K, v: Option<V>) -> Result<Self, ParseError>
    where
        K: AsRef<str>,
        V: AsRef<str>,
        SmallString: From<K> + From<V>,
    {
        match v {
            Some(v) => {
                self.parts.qualifiers.insert(k, v)?;
            },
            None => {
                self.parts.qualifiers.remove(k);
            },
        }
        Ok(self)
    }

    /// Unset a qualifier.
    ///
    /// This is the same as passing `k, None` to [`Self::with_qualifier`].
    pub fn without_qualifier<S>(mut self, k: S) -> Self
    where
        S: AsRef<str>,
        SmallString: From<S>,
    {
        self.parts.qualifiers.remove(k);
        self
    }

    /// Set the subpath.
    ///
    /// Passing `None` will unset the subpath.
    pub fn with_subpath<S>(mut self, new: Option<S>) -> Self
    where
        SmallString: From<S>,
    {
        self.parts.subpath = new.map(SmallString::from);
        self
    }

    /// Unset the subpath.
    ///
    /// This is the same as passing `None` to [`Self::with_subpath`].
    pub fn without_subpath(mut self) -> Self {
        self.parts.subpath = None;
        self
    }

    /// Convert the PURL builder into a PURL.
    ///
    /// The [`PurlShape::finish`] will be called on `T` to apply normalization
    /// and validation rules.
    pub fn build(mut self) -> Result<GenericPurl<T>, <T as PurlShape>::Error>
    where
        T: PurlShape,
    {
        self.package_type.finish(&mut self.parts)?;

        let GenericPurlBuilder { package_type, parts } = self;

        Ok(GenericPurl { package_type, parts })
    }
}

#[cfg(test)]
mod tests {
    use std::borrow::Cow;

    use maplit::hashmap;

    use super::*;
    use crate::qualifiers::Qualifiers;

    #[test]
    fn with_package_type_sets_type() {
        let builder = GenericPurlBuilder { package_type: "old", parts: PurlParts::default() }
            .with_package_type("new");
        assert_eq!("new", builder.package_type);
    }

    #[test]
    fn with_namespace_some_sets_namespace() {
        let builder = GenericPurlBuilder::<&str>::default().with_namespace(Some("new"));
        assert_eq!(Some("new"), builder.parts.namespace.as_deref());
    }

    #[test]
    fn with_namespace_none_unsets_namespace() {
        let builder = GenericPurlBuilder {
            package_type: "",
            parts: PurlParts { namespace: Some("old".into()), ..Default::default() },
        }
        .with_namespace(None::<&str>);
        assert_eq!(None, builder.parts.namespace);
    }

    #[test]
    fn without_namespace_unsets_namespace() {
        let builder = GenericPurlBuilder {
            package_type: "",
            parts: PurlParts { namespace: Some("old".into()), ..Default::default() },
        }
        .without_namespace();
        assert_eq!(None, builder.parts.namespace);
    }

    #[test]
    fn with_name_sets_name() {
        let builder = GenericPurlBuilder::<&str>::default().with_name("new");
        assert_eq!("new", &builder.parts.name);
    }

    #[test]
    fn with_version_some_sets_version() {
        let builder = GenericPurlBuilder::<&str>::default().with_version(Some("new"));
        assert_eq!(Some("new"), builder.parts.version.as_deref());
    }

    #[test]
    fn with_version_none_unsets_version() {
        let builder = GenericPurlBuilder {
            package_type: "",
            parts: PurlParts { version: Some("old".into()), ..Default::default() },
        }
        .with_version(None::<&str>);
        assert_eq!(None, builder.parts.version);
    }

    #[test]
    fn without_version_unsets_version() {
        let builder = GenericPurlBuilder {
            package_type: "",
            parts: PurlParts { version: Some("old".into()), ..Default::default() },
        }
        .without_version();
        assert_eq!(None, builder.parts.version);
    }

    #[test]
    fn with_qualifier_with_new_valid_key_and_some_value_sets_qualifier() {
        let builder =
            GenericPurlBuilder { package_type: "", parts: PurlParts { ..Default::default() } }
                .with_qualifier("ok", Some(""))
                .unwrap();
        assert_eq!(
            hashmap! { "ok" => "" },
            builder.parts.qualifiers.iter().map(|(k, v)| (k.as_str(), v)).collect(),
        )
    }

    #[test]
    fn with_qualifier_with_new_invalid_key_and_some_value_returns_error() {
        let result =
            GenericPurlBuilder { package_type: "", parts: PurlParts { ..Default::default() } }
                .with_qualifier("", Some(""));
        assert!(matches!(result, Err(ParseError::InvalidQualifier)));
    }

    #[test]
    fn with_qualifier_with_new_valid_key_and_none_value_does_nothing() {
        let builder =
            GenericPurlBuilder { package_type: "", parts: PurlParts { ..Default::default() } }
                .with_qualifier("ok", None::<&str>)
                .unwrap();
        assert_eq!(0, builder.parts.qualifiers.iter().len());
    }

    #[test]
    fn with_qualifier_with_new_invalid_key_and_none_value_does_nothing() {
        let builder =
            GenericPurlBuilder { package_type: "", parts: PurlParts { ..Default::default() } }
                .with_qualifier("", None::<&str>)
                .unwrap();
        assert_eq!(0, builder.parts.qualifiers.iter().len());
    }

    #[test]
    fn with_qualifier_with_existing_key_and_some_value_sets_qualifier() {
        let builder = GenericPurlBuilder {
            package_type: "",
            parts: PurlParts {
                qualifiers: Qualifiers::try_from_iter([("ok", "old")]).unwrap(),
                ..Default::default()
            },
        }
        .with_qualifier("ok", Some("new"))
        .unwrap();
        assert_eq!(
            hashmap! { "ok" => "new" },
            builder.parts.qualifiers.iter().map(|(k, v)| (k.as_str(), v)).collect(),
        )
    }

    #[test]
    fn with_qualifier_with_existing_key_and_none_value_unsets_qualifier() {
        let builder = GenericPurlBuilder {
            package_type: "",
            parts: PurlParts {
                qualifiers: Qualifiers::try_from_iter([("ok", "old")]).unwrap(),
                ..Default::default()
            },
        }
        .with_qualifier("ok", None::<&str>)
        .unwrap();
        assert_eq!(hashmap! {}, builder.parts.qualifiers.iter().collect())
    }

    #[test]
    fn without_qualifier_with_existing_key_unsets_qualifier() {
        let builder = GenericPurlBuilder {
            package_type: "",
            parts: PurlParts {
                qualifiers: Qualifiers::try_from_iter([("ok", "old")]).unwrap(),
                ..Default::default()
            },
        }
        .without_qualifier("ok");
        assert_eq!(hashmap! {}, builder.parts.qualifiers.iter().collect())
    }

    #[test]
    fn with_subpath_some_sets_subpath() {
        let builder = GenericPurlBuilder::<&str>::default().with_subpath(Some("new"));
        assert_eq!(Some("new"), builder.parts.subpath.as_deref());
    }

    #[test]
    fn with_subpath_none_unsets_subpath() {
        let builder = GenericPurlBuilder {
            package_type: "",
            parts: PurlParts { subpath: Some("old".into()), ..Default::default() },
        }
        .with_subpath(None::<&str>);
        assert_eq!(None, builder.parts.subpath);
    }

    #[test]
    fn without_subpath_unsets_subpath() {
        let builder = GenericPurlBuilder {
            package_type: "",
            parts: PurlParts { subpath: Some("old".into()), ..Default::default() },
        }
        .without_subpath();
        assert_eq!(None, builder.parts.subpath);
    }

    #[test]
    fn build_works() {
        let purl = GenericPurlBuilder::default()
            .with_package_type(Cow::Borrowed("type"))
            .with_namespace(Some("namespace"))
            .with_name("name")
            .with_version(Some("version"))
            .with_qualifier("key", Some("value"))
            .unwrap()
            .with_subpath(Some("subpath"))
            .build()
            .expect("build failed");
        assert_eq!("type", purl.package_type().package_type());
        assert_eq!("name", purl.name());
        assert_eq!(Some("version"), purl.version());
        assert_eq!(Some("value"), purl.qualifiers().get("key"));
        assert_eq!(Some("subpath"), purl.subpath());
    }
}