[PURL] parsing, manipulation, and formatting.

A PURL is an identifier that refers to a software package. For example,
`pkg:cargo/phylum-purl` refers to this package.

[PURL]: https://github.com/package-url/purl-spec

# Example

```rust
use std::str::FromStr;

use phylum_purl::{PackageType, Purl};

# fn main() -> Result<(), Box<dyn std::error::Error>> {
let purl = Purl::from_str(
    "pkg:NPM/@acme/example@1.2.3?Checksum=sha256:\
     E3B0C44298FC1C149AFBF4C8996FB92427AE41E4649B934CA495991B7852B855",
)?;
assert_eq!(&PackageType::Npm, purl.package_type());
assert_eq!(Some("@acme"), purl.namespace());
assert_eq!("example", purl.name());
assert_eq!(Some("1.2.3"), purl.version());
// Normalization is performed during parsing.
assert_eq!(
    "sha256:e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
    purl.qualifiers()["checksum"],
);
assert_eq!(
    "pkg:npm/%40acme/example@1.2.3?checksum=sha256:\
     e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
    &purl.to_string(),
);

let purl = purl.into_builder().without_version().without_qualifier("checksum").build()?;
assert_eq!("pkg:npm/%40acme/example", &purl.to_string(),);
# Ok(())
# }
```

# Features

- package-type: [`PackageType`] and related types
- serde: PURLs can be serialized and deserialized from strings
- smartstring: The smartstring crate is used to reduce heap allocations
