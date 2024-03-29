use std::collections::HashMap;
use std::fs;
use std::io::{BufWriter, Write};
use std::str::FromStr;

use convert_case::{Case, Casing};
use lazy_static::lazy_static;
use proc_macro2::{Span, TokenStream};
use purl::PackageType;
use quote::{format_ident, quote};
use regex::Regex;
use serde::Deserialize;
use syn::{parse_quote, Ident};

use crate::workspace_dir;

const TEST_SUITE_DATA: &str = include_str!("generate_tests/test-suite-data.json");
const PHYLUM_TEST_SUITE_DATA: &str = include_str!("generate_tests/phylum-test-suite-data.json");
const BLACKLIST: &[&str] = &[
    // NuGet package names are not case sensitive. package-url/purl-spec#226
    "nuget names are case sensitive",
    // These tests fail because we don't support type-specific rules for these types.
    "bitbucket namespace and name should be lowercased",
    "composer names are not case sensitive",
    "github namespace and name should be lowercased",
    "Hugging Face model with various cases",
    "MLflow model tracked in Azure Databricks (case insensitive)",
];

lazy_static! {
    static ref UNDERSCORES: Regex = Regex::new("__+").unwrap();
}

#[derive(Deserialize)]
struct Test<'a> {
    description: &'a str,
    purl: &'a str,
    canonical_purl: Option<&'a str>,
    r#type: Option<&'a str>,
    namespace: Option<&'a str>,
    name: Option<&'a str>,
    version: Option<&'a str>,
    qualifiers: Option<HashMap<&'a str, &'a str>>,
    subpath: Option<&'a str>,
    is_invalid: bool,
}

pub fn main() {
    let purl_tests: Vec<Test> =
        serde_json::from_str(TEST_SUITE_DATA).expect("Could not read test-suite-data.json");
    let phylum_tests: Vec<Test> = serde_json::from_str(PHYLUM_TEST_SUITE_DATA)
        .expect("Could not read phylum-test-suite-data.json");

    let tests = purl_tests
        .into_iter()
        .chain(phylum_tests)
        .filter(|t| !BLACKLIST.contains(&t.description))
        .map(test_to_tokens);
    let suite = parse_quote! {
        use std::collections::HashMap;
        use std::str::FromStr;
        use purl::{GenericPurl, PackageError, PackageType, Purl};

        #(#tests)*
    };

    let file = fs::File::create(workspace_dir().join("purl_test/src/lib.rs"))
        .expect("Could not create test_suite.rs");
    let mut file = BufWriter::new(file);

    writeln!(file, "// This file is autogenerated by generate_tests.rs.").unwrap();
    writeln!(file, "// Use `cargo xtask codegen` to regenerate it.").unwrap();
    writeln!(file, "#![cfg(test)]").unwrap();
    writeln!(file).unwrap();
    writeln!(file, "{}", prettyplease::unparse(&suite)).unwrap();
}

fn test_to_tokens(test: Test) -> Option<TokenStream> {
    let Test {
        description,
        purl,
        canonical_purl,
        r#type,
        namespace,
        name,
        version,
        qualifiers,
        subpath,
        is_invalid,
    } = test;
    let test_name = format_ident!(
        "{}",
        UNDERSCORES.replace_all(
            &description.to_case(Case::Snake).replace(|c: char| !c.is_alphanumeric(), "_"),
            "_"
        )
    );
    let parsed_type = r#type.and_then(|t| PackageType::from_str(t).ok());
    Some(if is_invalid {
        quote! {
            #[test]
            #[doc = #description]
            fn #test_name() {
                assert!(Purl::from_str(#purl).is_err(), "{}", #description);
            }
        }
    } else {
        let canonicalized_binding = Ident::new("canonicalized", Span::call_site());

        let name = name.expect("Valid test must have package name");
        let namespace = option_to_tokens(namespace);
        let version = option_to_tokens(version);
        let subpath = option_to_tokens(subpath);
        let qualifiers = qualifiers_to_tokens(qualifiers);

        // Check if this type is supported by this library.
        let expected_type;
        let parse;
        let parse_canonical;
        if let Some(parsed_type) = parsed_type {
            let type_tokens = type_to_tokens(parsed_type);
            expected_type = quote! { &#type_tokens };
            parse = quote! {
                match Purl::from_str(#purl) {
                    Ok(purl) => purl,
                    Err(error) => panic!("Failed to parse valid purl {:?}: {}", #purl, error),
                }
            };
            parse_canonical = quote! {
                match Purl::from_str(&#canonicalized_binding) {
                    Ok(purl) => purl,
                    Err(error) => panic!("Failed to parse canonical purl {:?}: {}", #purl, error),
                }
            };
        } else {
            // For all the unsupported cases, we can still verify the ability to handle them
            // without type-specific rules.
            // If the type-specific rules are required for the test to pass, the test needs
            // to be added to BLACKLIST.
            expected_type = quote! { #r#type };
            parse = quote! {
                {
                    // Purl (GenericPurl<PackageType>) should return an error.
                    assert!(matches!(Purl::from_str(#purl), Err(PackageError::UnsupportedType)), "Type {} is not supported", #r#type);

                    match GenericPurl::<String>::from_str(#purl) {
                        Ok(purl) => purl,
                        Err(error) => panic!("Failed to parse valid purl {:?}: {}", #purl, error),
                    }
                }
            };
            parse_canonical = quote! {
                match GenericPurl::<String>::from_str(&#canonicalized_binding) {
                    Ok(purl) => purl,
                    Err(error) => panic!("Failed to parse valid purl {:?}: {}", #purl, error),
                }
            };
        }

        quote! {
            #[test]
            #[doc = #description]
            fn #test_name() {
                let parsed = #parse;
                assert_eq!(#expected_type, parsed.package_type(), "Incorrect package type");
                assert_eq!(#namespace, parsed.namespace(), "Incorrect namespace");
                assert_eq!(#name, parsed.name(), "Incorrect name");
                assert_eq!(#version, parsed.version(), "Incorrect version");
                assert_eq!(#subpath, parsed.subpath(), "Incorrect subpath");
                assert_eq!(#qualifiers, parsed.qualifiers().iter().map(|(k, v)| (k.as_str(), v)).collect::<HashMap<&str, &str>>(), "Incorrect qualifiers");

                let #canonicalized_binding = parsed.to_string();
                assert_eq!(#canonical_purl, #canonicalized_binding, "Incorrect string representation");

                let parsed_canonical = #parse_canonical;
                assert_eq!(#expected_type, parsed_canonical.package_type(), "Incorrect package type for canonicalized PURL");
                assert_eq!(#namespace, parsed_canonical.namespace(), "Incorrect namespace for canonicalized PURL");
                assert_eq!(#name, parsed_canonical.name(), "Incorrect name for canonicalized PURL");
                assert_eq!(#version, parsed_canonical.version(), "Incorrect version for canonicalized PURL");
                assert_eq!(#subpath, parsed_canonical.subpath(), "Incorrect subpath for canonicalized PURL");
                assert_eq!(#qualifiers, parsed_canonical.qualifiers().iter().map(|(k, v)| (k.as_str(), v)).collect::<HashMap<&str, &str>>(), "Incorrect qualifiers for canonicalized PURL");
            }
        }
    })
}

fn type_to_tokens(value: PackageType) -> TokenStream {
    let ident = format_ident!("{}", format!("{:?}", value));
    quote! { PackageType::#ident }
}

fn option_to_tokens(value: Option<&str>) -> TokenStream {
    if let Some(value) = value {
        quote! { Some(#value) }
    } else {
        quote! { None }
    }
}

fn qualifiers_to_tokens(value: Option<HashMap<&str, &str>>) -> TokenStream {
    let mut value: Vec<(&str, &str)> = value.unwrap_or_default().into_iter().collect();
    value.sort_unstable();
    if value.is_empty() {
        quote! { HashMap::<&str, &str>::new() }
    } else {
        let entries = value.into_iter().map(|(k, v)| quote! { (#k, #v) });
        quote! { [#(#entries),*].into_iter().collect::<HashMap<&str, &str>>() }
    }
}
