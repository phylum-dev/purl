// This file is autogenerated by generate_tests.rs.
// Use `cargo xtask codegen` to regenerate it.
#![cfg(test)]

use std::collections::HashMap;
use std::str::FromStr;

use phylum_purl::{PackageError, PackageType, Purl};
#[test]
/// valid maven purl
fn valid_maven_purl() {
    let parsed = match Purl::from_str("pkg:maven/org.apache.commons/io@1.3.4") {
        Ok(purl) => purl,
        Err(error) => {
            panic!(
                "Failed to parse valid purl {:?}: {}",
                "pkg:maven/org.apache.commons/io@1.3.4", error
            )
        },
    };
    assert_eq!(&PackageType::Maven, parsed.package_type(), "Incorrect package type");
    assert_eq!(Some("org.apache.commons"), parsed.namespace(), "Incorrect namespace");
    assert_eq!("io", parsed.name(), "Incorrect name");
    assert_eq!(Some("1.3.4"), parsed.version(), "Incorrect version");
    assert_eq!(None, parsed.subpath(), "Incorrect subpath");
    let expected_qualifiers: HashMap<&str, &str> = HashMap::new();
    assert_eq!(
        expected_qualifiers,
        parsed.qualifiers().iter().map(|(k, v)| (k.as_str(), v)).collect::<HashMap<&str, &str>>()
    );
    assert_eq!(
        "pkg:maven/org.apache.commons/io@1.3.4",
        &parsed.to_string(),
        "Incorrect string representation"
    );
}
#[test]
/// basic valid maven purl without version
fn basic_valid_maven_purl_without_version() {
    let parsed = match Purl::from_str("pkg:maven/org.apache.commons/io") {
        Ok(purl) => purl,
        Err(error) => {
            panic!("Failed to parse valid purl {:?}: {}", "pkg:maven/org.apache.commons/io", error)
        },
    };
    assert_eq!(&PackageType::Maven, parsed.package_type(), "Incorrect package type");
    assert_eq!(Some("org.apache.commons"), parsed.namespace(), "Incorrect namespace");
    assert_eq!("io", parsed.name(), "Incorrect name");
    assert_eq!(None, parsed.version(), "Incorrect version");
    assert_eq!(None, parsed.subpath(), "Incorrect subpath");
    let expected_qualifiers: HashMap<&str, &str> = HashMap::new();
    assert_eq!(
        expected_qualifiers,
        parsed.qualifiers().iter().map(|(k, v)| (k.as_str(), v)).collect::<HashMap<&str, &str>>()
    );
    assert_eq!(
        "pkg:maven/org.apache.commons/io",
        &parsed.to_string(),
        "Incorrect string representation"
    );
}
#[test]
/// valid go purl without version and with subpath
fn valid_go_purl_without_version_and_with_subpath() {
    let parsed = match Purl::from_str(
        "pkg:GOLANG/google.golang.org/genproto#/googleapis/api/annotations/",
    ) {
        Ok(purl) => purl,
        Err(error) => {
            panic!(
                "Failed to parse valid purl {:?}: {}",
                "pkg:GOLANG/google.golang.org/genproto#/googleapis/api/annotations/", error
            )
        },
    };
    assert_eq!(&PackageType::Golang, parsed.package_type(), "Incorrect package type");
    assert_eq!(Some("google.golang.org"), parsed.namespace(), "Incorrect namespace");
    assert_eq!("genproto", parsed.name(), "Incorrect name");
    assert_eq!(None, parsed.version(), "Incorrect version");
    assert_eq!(Some("googleapis/api/annotations"), parsed.subpath(), "Incorrect subpath");
    let expected_qualifiers: HashMap<&str, &str> = HashMap::new();
    assert_eq!(
        expected_qualifiers,
        parsed.qualifiers().iter().map(|(k, v)| (k.as_str(), v)).collect::<HashMap<&str, &str>>()
    );
    assert_eq!(
        "pkg:golang/google.golang.org/genproto#googleapis/api/annotations",
        &parsed.to_string(),
        "Incorrect string representation"
    );
}
#[test]
/// valid go purl with version and subpath
fn valid_go_purl_with_version_and_subpath() {
    let parsed = match Purl::from_str(
        "pkg:GOLANG/google.golang.org/genproto@abcdedf#/googleapis/api/annotations/",
    ) {
        Ok(purl) => purl,
        Err(error) => {
            panic!(
                "Failed to parse valid purl {:?}: {}",
                "pkg:GOLANG/google.golang.org/genproto@abcdedf#/googleapis/api/annotations/", error
            )
        },
    };
    assert_eq!(&PackageType::Golang, parsed.package_type(), "Incorrect package type");
    assert_eq!(Some("google.golang.org"), parsed.namespace(), "Incorrect namespace");
    assert_eq!("genproto", parsed.name(), "Incorrect name");
    assert_eq!(Some("abcdedf"), parsed.version(), "Incorrect version");
    assert_eq!(Some("googleapis/api/annotations"), parsed.subpath(), "Incorrect subpath");
    let expected_qualifiers: HashMap<&str, &str> = HashMap::new();
    assert_eq!(
        expected_qualifiers,
        parsed.qualifiers().iter().map(|(k, v)| (k.as_str(), v)).collect::<HashMap<&str, &str>>()
    );
    assert_eq!(
        "pkg:golang/google.golang.org/genproto@abcdedf#googleapis/api/annotations",
        &parsed.to_string(),
        "Incorrect string representation"
    );
}
#[test]
/// unsupported: bitbucket namespace and name should be lowercased
fn unsupported_bitbucket_namespace_and_name_should_be_lowercased() {
    assert!(
        matches!(
            Purl::from_str("pkg:bitbucket/birKenfeld/pyGments-main@244fd47e07d1014f0aed9c"),
            Err(PackageError::UnsupportedType)
        ),
        "Type {} is not supported",
        "bitbucket"
    );
}
#[test]
/// unsupported: github namespace and name should be lowercased
fn unsupported_github_namespace_and_name_should_be_lowercased() {
    assert!(
        matches!(
            Purl::from_str("pkg:github/Package-url/purl-Spec@244fd47e07d1004f0aed9c"),
            Err(PackageError::UnsupportedType)
        ),
        "Type {} is not supported",
        "github"
    );
}
#[test]
/// unsupported: debian can use qualifiers
fn unsupported_debian_can_use_qualifiers() {
    assert!(
        matches!(
            Purl::from_str("pkg:deb/debian/curl@7.50.3-1?arch=i386&distro=jessie"),
            Err(PackageError::UnsupportedType)
        ),
        "Type {} is not supported",
        "deb"
    );
}
#[test]
/// unsupported: docker uses qualifiers and hash image id as versions
fn unsupported_docker_uses_qualifiers_and_hash_image_id_as_versions() {
    assert!(
        matches!(
            Purl::from_str(
                "pkg:docker/customer/dockerimage@sha256:244fd47e07d1004f0aed9c?repository_url=gcr.\
                 io"
            ),
            Err(PackageError::UnsupportedType)
        ),
        "Type {} is not supported",
        "docker"
    );
}
#[test]
/// Java gem can use a qualifier
fn java_gem_can_use_a_qualifier() {
    let parsed = match Purl::from_str("pkg:gem/jruby-launcher@1.1.2?Platform=java") {
        Ok(purl) => purl,
        Err(error) => {
            panic!(
                "Failed to parse valid purl {:?}: {}",
                "pkg:gem/jruby-launcher@1.1.2?Platform=java", error
            )
        },
    };
    assert_eq!(&PackageType::Gem, parsed.package_type(), "Incorrect package type");
    assert_eq!(None, parsed.namespace(), "Incorrect namespace");
    assert_eq!("jruby-launcher", parsed.name(), "Incorrect name");
    assert_eq!(Some("1.1.2"), parsed.version(), "Incorrect version");
    assert_eq!(None, parsed.subpath(), "Incorrect subpath");
    let expected_qualifiers: HashMap<&str, &str> = [("platform", "java")].into_iter().collect();
    assert_eq!(
        expected_qualifiers,
        parsed.qualifiers().iter().map(|(k, v)| (k.as_str(), v)).collect::<HashMap<&str, &str>>()
    );
    assert_eq!(
        "pkg:gem/jruby-launcher@1.1.2?platform=java",
        &parsed.to_string(),
        "Incorrect string representation"
    );
}
#[test]
/// maven often uses qualifiers
fn maven_often_uses_qualifiers() {
    let parsed = match Purl::from_str(
        "pkg:Maven/org.apache.xmlgraphics/batik-anim@1.9.1?classifier=sources&repositorY_url=repo.\
         spring.io/release",
    ) {
        Ok(purl) => purl,
        Err(error) => {
            panic!(
                "Failed to parse valid purl {:?}: {}",
                "pkg:Maven/org.apache.xmlgraphics/batik-anim@1.9.1?classifier=sources&\
                 repositorY_url=repo.spring.io/release",
                error
            )
        },
    };
    assert_eq!(&PackageType::Maven, parsed.package_type(), "Incorrect package type");
    assert_eq!(Some("org.apache.xmlgraphics"), parsed.namespace(), "Incorrect namespace");
    assert_eq!("batik-anim", parsed.name(), "Incorrect name");
    assert_eq!(Some("1.9.1"), parsed.version(), "Incorrect version");
    assert_eq!(None, parsed.subpath(), "Incorrect subpath");
    let expected_qualifiers: HashMap<&str, &str> =
        [("classifier", "sources"), ("repository_url", "repo.spring.io/release")]
            .into_iter()
            .collect();
    assert_eq!(
        expected_qualifiers,
        parsed.qualifiers().iter().map(|(k, v)| (k.as_str(), v)).collect::<HashMap<&str, &str>>()
    );
    assert_eq!(
        "pkg:maven/org.apache.xmlgraphics/batik-anim@1.9.1?classifier=sources&repository_url=repo.\
         spring.io/release",
        &parsed.to_string(),
        "Incorrect string representation"
    );
}
#[test]
/// maven pom reference
fn maven_pom_reference() {
    let parsed = match Purl::from_str(
        "pkg:Maven/org.apache.xmlgraphics/batik-anim@1.9.1?extension=pom&repositorY_url=repo.\
         spring.io/release",
    ) {
        Ok(purl) => purl,
        Err(error) => {
            panic!(
                "Failed to parse valid purl {:?}: {}",
                "pkg:Maven/org.apache.xmlgraphics/batik-anim@1.9.1?extension=pom&\
                 repositorY_url=repo.spring.io/release",
                error
            )
        },
    };
    assert_eq!(&PackageType::Maven, parsed.package_type(), "Incorrect package type");
    assert_eq!(Some("org.apache.xmlgraphics"), parsed.namespace(), "Incorrect namespace");
    assert_eq!("batik-anim", parsed.name(), "Incorrect name");
    assert_eq!(Some("1.9.1"), parsed.version(), "Incorrect version");
    assert_eq!(None, parsed.subpath(), "Incorrect subpath");
    let expected_qualifiers: HashMap<&str, &str> =
        [("extension", "pom"), ("repository_url", "repo.spring.io/release")].into_iter().collect();
    assert_eq!(
        expected_qualifiers,
        parsed.qualifiers().iter().map(|(k, v)| (k.as_str(), v)).collect::<HashMap<&str, &str>>()
    );
    assert_eq!(
        "pkg:maven/org.apache.xmlgraphics/batik-anim@1.9.1?extension=pom&repository_url=repo.\
         spring.io/release",
        &parsed.to_string(),
        "Incorrect string representation"
    );
}
#[test]
/// maven can come with a type qualifier
fn maven_can_come_with_a_type_qualifier() {
    let parsed =
        match Purl::from_str("pkg:Maven/net.sf.jacob-project/jacob@1.14.3?classifier=x86&type=dll")
        {
            Ok(purl) => purl,
            Err(error) => {
                panic!(
                    "Failed to parse valid purl {:?}: {}",
                    "pkg:Maven/net.sf.jacob-project/jacob@1.14.3?classifier=x86&type=dll", error
                )
            },
        };
    assert_eq!(&PackageType::Maven, parsed.package_type(), "Incorrect package type");
    assert_eq!(Some("net.sf.jacob-project"), parsed.namespace(), "Incorrect namespace");
    assert_eq!("jacob", parsed.name(), "Incorrect name");
    assert_eq!(Some("1.14.3"), parsed.version(), "Incorrect version");
    assert_eq!(None, parsed.subpath(), "Incorrect subpath");
    let expected_qualifiers: HashMap<&str, &str> =
        [("classifier", "x86"), ("type", "dll")].into_iter().collect();
    assert_eq!(
        expected_qualifiers,
        parsed.qualifiers().iter().map(|(k, v)| (k.as_str(), v)).collect::<HashMap<&str, &str>>()
    );
    assert_eq!(
        "pkg:maven/net.sf.jacob-project/jacob@1.14.3?classifier=x86&type=dll",
        &parsed.to_string(),
        "Incorrect string representation"
    );
}
#[test]
/// npm can be scoped
fn npm_can_be_scoped() {
    let parsed = match Purl::from_str("pkg:npm/%40angular/animation@12.3.1") {
        Ok(purl) => purl,
        Err(error) => {
            panic!(
                "Failed to parse valid purl {:?}: {}",
                "pkg:npm/%40angular/animation@12.3.1", error
            )
        },
    };
    assert_eq!(&PackageType::Npm, parsed.package_type(), "Incorrect package type");
    assert_eq!(Some("@angular"), parsed.namespace(), "Incorrect namespace");
    assert_eq!("animation", parsed.name(), "Incorrect name");
    assert_eq!(Some("12.3.1"), parsed.version(), "Incorrect version");
    assert_eq!(None, parsed.subpath(), "Incorrect subpath");
    let expected_qualifiers: HashMap<&str, &str> = HashMap::new();
    assert_eq!(
        expected_qualifiers,
        parsed.qualifiers().iter().map(|(k, v)| (k.as_str(), v)).collect::<HashMap<&str, &str>>()
    );
    assert_eq!(
        "pkg:npm/%40angular/animation@12.3.1",
        &parsed.to_string(),
        "Incorrect string representation"
    );
}
#[test]
/// pypi names have special rules and not case sensitive
fn pypi_names_have_special_rules_and_not_case_sensitive() {
    let parsed = match Purl::from_str("pkg:PYPI/Django_package@1.11.1.dev1") {
        Ok(purl) => purl,
        Err(error) => {
            panic!(
                "Failed to parse valid purl {:?}: {}",
                "pkg:PYPI/Django_package@1.11.1.dev1", error
            )
        },
    };
    assert_eq!(&PackageType::PyPI, parsed.package_type(), "Incorrect package type");
    assert_eq!(None, parsed.namespace(), "Incorrect namespace");
    assert_eq!("django-package", parsed.name(), "Incorrect name");
    assert_eq!(Some("1.11.1.dev1"), parsed.version(), "Incorrect version");
    assert_eq!(None, parsed.subpath(), "Incorrect subpath");
    let expected_qualifiers: HashMap<&str, &str> = HashMap::new();
    assert_eq!(
        expected_qualifiers,
        parsed.qualifiers().iter().map(|(k, v)| (k.as_str(), v)).collect::<HashMap<&str, &str>>()
    );
    assert_eq!(
        "pkg:pypi/django-package@1.11.1.dev1",
        &parsed.to_string(),
        "Incorrect string representation"
    );
}
#[test]
/// unsupported: rpm often use qualifiers
fn unsupported_rpm_often_use_qualifiers() {
    assert!(
        matches!(
            Purl::from_str("pkg:Rpm/fedora/curl@7.50.3-1.fc25?Arch=i386&Distro=fedora-25"),
            Err(PackageError::UnsupportedType)
        ),
        "Type {} is not supported",
        "rpm"
    );
}
#[test]
/// a scheme is always required
fn a_scheme_is_always_required() {
    assert!(
        Purl::from_str("EnterpriseLibrary.Common@6.0.1304").is_err(),
        "{}",
        "a scheme is always required"
    );
}
#[test]
/// a type is always required
fn a_type_is_always_required() {
    assert!(
        Purl::from_str("pkg:EnterpriseLibrary.Common@6.0.1304").is_err(),
        "{}",
        "a type is always required"
    );
}
#[test]
/// a name is required
fn a_name_is_required() {
    assert!(Purl::from_str("pkg:maven/@1.3.4").is_err(), "{}", "a name is required");
}
#[test]
/// slash / after scheme is not significant
fn slash_after_scheme_is_not_significant() {
    let parsed = match Purl::from_str("pkg:/maven/org.apache.commons/io") {
        Ok(purl) => purl,
        Err(error) => {
            panic!("Failed to parse valid purl {:?}: {}", "pkg:/maven/org.apache.commons/io", error)
        },
    };
    assert_eq!(&PackageType::Maven, parsed.package_type(), "Incorrect package type");
    assert_eq!(Some("org.apache.commons"), parsed.namespace(), "Incorrect namespace");
    assert_eq!("io", parsed.name(), "Incorrect name");
    assert_eq!(None, parsed.version(), "Incorrect version");
    assert_eq!(None, parsed.subpath(), "Incorrect subpath");
    let expected_qualifiers: HashMap<&str, &str> = HashMap::new();
    assert_eq!(
        expected_qualifiers,
        parsed.qualifiers().iter().map(|(k, v)| (k.as_str(), v)).collect::<HashMap<&str, &str>>()
    );
    assert_eq!(
        "pkg:maven/org.apache.commons/io",
        &parsed.to_string(),
        "Incorrect string representation"
    );
}
#[test]
/// double slash // after scheme is not significant
fn double_slash_after_scheme_is_not_significant() {
    let parsed = match Purl::from_str("pkg://maven/org.apache.commons/io") {
        Ok(purl) => purl,
        Err(error) => {
            panic!(
                "Failed to parse valid purl {:?}: {}",
                "pkg://maven/org.apache.commons/io", error
            )
        },
    };
    assert_eq!(&PackageType::Maven, parsed.package_type(), "Incorrect package type");
    assert_eq!(Some("org.apache.commons"), parsed.namespace(), "Incorrect namespace");
    assert_eq!("io", parsed.name(), "Incorrect name");
    assert_eq!(None, parsed.version(), "Incorrect version");
    assert_eq!(None, parsed.subpath(), "Incorrect subpath");
    let expected_qualifiers: HashMap<&str, &str> = HashMap::new();
    assert_eq!(
        expected_qualifiers,
        parsed.qualifiers().iter().map(|(k, v)| (k.as_str(), v)).collect::<HashMap<&str, &str>>()
    );
    assert_eq!(
        "pkg:maven/org.apache.commons/io",
        &parsed.to_string(),
        "Incorrect string representation"
    );
}
#[test]
/// slash /// after type  is not significant
fn slash_after_type_is_not_significant() {
    let parsed = match Purl::from_str("pkg:///maven/org.apache.commons/io") {
        Ok(purl) => purl,
        Err(error) => {
            panic!(
                "Failed to parse valid purl {:?}: {}",
                "pkg:///maven/org.apache.commons/io", error
            )
        },
    };
    assert_eq!(&PackageType::Maven, parsed.package_type(), "Incorrect package type");
    assert_eq!(Some("org.apache.commons"), parsed.namespace(), "Incorrect namespace");
    assert_eq!("io", parsed.name(), "Incorrect name");
    assert_eq!(None, parsed.version(), "Incorrect version");
    assert_eq!(None, parsed.subpath(), "Incorrect subpath");
    let expected_qualifiers: HashMap<&str, &str> = HashMap::new();
    assert_eq!(
        expected_qualifiers,
        parsed.qualifiers().iter().map(|(k, v)| (k.as_str(), v)).collect::<HashMap<&str, &str>>()
    );
    assert_eq!(
        "pkg:maven/org.apache.commons/io",
        &parsed.to_string(),
        "Incorrect string representation"
    );
}
#[test]
/// valid maven purl with case sensitive namespace and name
fn valid_maven_purl_with_case_sensitive_namespace_and_name() {
    let parsed = match Purl::from_str("pkg:maven/HTTPClient/HTTPClient@0.3-3") {
        Ok(purl) => purl,
        Err(error) => {
            panic!(
                "Failed to parse valid purl {:?}: {}",
                "pkg:maven/HTTPClient/HTTPClient@0.3-3", error
            )
        },
    };
    assert_eq!(&PackageType::Maven, parsed.package_type(), "Incorrect package type");
    assert_eq!(Some("HTTPClient"), parsed.namespace(), "Incorrect namespace");
    assert_eq!("HTTPClient", parsed.name(), "Incorrect name");
    assert_eq!(Some("0.3-3"), parsed.version(), "Incorrect version");
    assert_eq!(None, parsed.subpath(), "Incorrect subpath");
    let expected_qualifiers: HashMap<&str, &str> = HashMap::new();
    assert_eq!(
        expected_qualifiers,
        parsed.qualifiers().iter().map(|(k, v)| (k.as_str(), v)).collect::<HashMap<&str, &str>>()
    );
    assert_eq!(
        "pkg:maven/HTTPClient/HTTPClient@0.3-3",
        &parsed.to_string(),
        "Incorrect string representation"
    );
}
#[test]
/// valid maven purl containing a space in the version and qualifier
fn valid_maven_purl_containing_a_space_in_the_version_and_qualifier() {
    let parsed = match Purl::from_str("pkg:maven/mygroup/myartifact@1.0.0%20Final?mykey=my%20value")
    {
        Ok(purl) => purl,
        Err(error) => {
            panic!(
                "Failed to parse valid purl {:?}: {}",
                "pkg:maven/mygroup/myartifact@1.0.0%20Final?mykey=my%20value", error
            )
        },
    };
    assert_eq!(&PackageType::Maven, parsed.package_type(), "Incorrect package type");
    assert_eq!(Some("mygroup"), parsed.namespace(), "Incorrect namespace");
    assert_eq!("myartifact", parsed.name(), "Incorrect name");
    assert_eq!(Some("1.0.0 Final"), parsed.version(), "Incorrect version");
    assert_eq!(None, parsed.subpath(), "Incorrect subpath");
    let expected_qualifiers: HashMap<&str, &str> = [("mykey", "my value")].into_iter().collect();
    assert_eq!(
        expected_qualifiers,
        parsed.qualifiers().iter().map(|(k, v)| (k.as_str(), v)).collect::<HashMap<&str, &str>>()
    );
    assert_eq!(
        "pkg:maven/mygroup/myartifact@1.0.0%20Final?mykey=my%20value",
        &parsed.to_string(),
        "Incorrect string representation"
    );
}
#[test]
/// checks for invalid qualifier keys
fn checks_for_invalid_qualifier_keys() {
    assert!(
        Purl::from_str("pkg:npm/myartifact@1.0.0?in%20production=true").is_err(),
        "{}",
        "checks for invalid qualifier keys"
    );
}
#[test]
/// unsupported: valid conan purl
fn unsupported_valid_conan_purl() {
    assert!(
        matches!(Purl::from_str("pkg:conan/cctz@2.3"), Err(PackageError::UnsupportedType)),
        "Type {} is not supported",
        "conan"
    );
}
#[test]
/// unsupported: valid conan purl with namespace and qualifier channel
fn unsupported_valid_conan_purl_with_namespace_and_qualifier_channel() {
    assert!(
        matches!(
            Purl::from_str("pkg:conan/bincrafters/cctz@2.3?channel=stable"),
            Err(PackageError::UnsupportedType)
        ),
        "Type {} is not supported",
        "conan"
    );
}
#[test]
/// invalid conan purl only namespace
fn invalid_conan_purl_only_namespace() {
    assert!(
        Purl::from_str("pkg:conan/bincrafters/cctz@2.3").is_err(),
        "{}",
        "invalid conan purl only namespace"
    );
}
#[test]
/// invalid conan purl only channel qualifier
fn invalid_conan_purl_only_channel_qualifier() {
    assert!(
        Purl::from_str("pkg:conan/cctz@2.3?channel=stable").is_err(),
        "{}",
        "invalid conan purl only channel qualifier"
    );
}
#[test]
/// unsupported: valid conda purl with qualifiers
fn unsupported_valid_conda_purl_with_qualifiers() {
    assert!(
        matches!(
            Purl::from_str(
                "pkg:conda/absl-py@0.4.1?build=py36h06a4308_0&channel=main&subdir=linux-64&\
                 type=tar.bz2"
            ),
            Err(PackageError::UnsupportedType)
        ),
        "Type {} is not supported",
        "conda"
    );
}
#[test]
/// unsupported: valid cran purl
fn unsupported_valid_cran_purl() {
    assert!(
        matches!(Purl::from_str("pkg:cran/A3@0.9.1"), Err(PackageError::UnsupportedType)),
        "Type {} is not supported",
        "cran"
    );
}
#[test]
/// invalid cran purl without name
fn invalid_cran_purl_without_name() {
    assert!(Purl::from_str("pkg:cran/@0.9.1").is_err(), "{}", "invalid cran purl without name");
}
#[test]
/// invalid cran purl without version
fn invalid_cran_purl_without_version() {
    assert!(Purl::from_str("pkg:cran/A3").is_err(), "{}", "invalid cran purl without version");
}
#[test]
/// unsupported: valid swift purl
fn unsupported_valid_swift_purl() {
    assert!(
        matches!(
            Purl::from_str("pkg:swift/github.com/Alamofire/Alamofire@5.4.3"),
            Err(PackageError::UnsupportedType)
        ),
        "Type {} is not supported",
        "swift"
    );
}
#[test]
/// invalid swift purl without namespace
fn invalid_swift_purl_without_namespace() {
    assert!(
        Purl::from_str("pkg:swift/Alamofire@5.4.3").is_err(),
        "{}",
        "invalid swift purl without namespace"
    );
}
#[test]
/// invalid swift purl without name
fn invalid_swift_purl_without_name() {
    assert!(
        Purl::from_str("pkg:swift/github.com/Alamofire/@5.4.3").is_err(),
        "{}",
        "invalid swift purl without name"
    );
}
#[test]
/// invalid swift purl without version
fn invalid_swift_purl_without_version() {
    assert!(
        Purl::from_str("pkg:swift/github.com/Alamofire/Alamofire").is_err(),
        "{}",
        "invalid swift purl without version"
    );
}
#[test]
/// unsupported: valid hackage purl
fn unsupported_valid_hackage_purl() {
    assert!(
        matches!(
            Purl::from_str("pkg:hackage/AC-HalfInteger@1.2.1"),
            Err(PackageError::UnsupportedType)
        ),
        "Type {} is not supported",
        "hackage"
    );
}
#[test]
/// name and version are always required
fn name_and_version_are_always_required() {
    assert!(Purl::from_str("pkg:hackage").is_err(), "{}", "name and version are always required");
}
#[test]
/// unsupported: minimal Hugging Face model
fn unsupported_minimal_hugging_face_model() {
    assert!(
        matches!(
            Purl::from_str(
                "pkg:huggingface/distilbert-base-uncased@043235d6088ecd3dd5fb5ca3592b6913fd516027"
            ),
            Err(PackageError::UnsupportedType)
        ),
        "Type {} is not supported",
        "huggingface"
    );
}
#[test]
/// unsupported: Hugging Face model with staging endpoint
fn unsupported_hugging_face_model_with_staging_endpoint() {
    assert!(
        matches!(Purl::from_str("pkg:huggingface/microsoft/deberta-v3-base@559062ad13d311b87b2c455e67dcd5f1c8f65111?repository_url=https://hub-ci.huggingface.co"),
        Err(PackageError::UnsupportedType)), "Type {} is not supported", "huggingface"
    );
}
#[test]
/// unsupported: Hugging Face model with various cases
fn unsupported_hugging_face_model_with_various_cases() {
    assert!(
        matches!(
            Purl::from_str(
                "pkg:huggingface/EleutherAI/gpt-neo-1.3B@797174552AE47F449AB70B684CABCB6603E5E85E"
            ),
            Err(PackageError::UnsupportedType)
        ),
        "Type {} is not supported",
        "huggingface"
    );
}
#[test]
/// unsupported: MLflow model tracked in Azure Databricks (case insensitive)
fn unsupported_m_lflow_model_tracked_in_azure_databricks_case_insensitive_() {
    assert!(
        matches!(Purl::from_str("pkg:mlflow/CreditFraud@3?repository_url=https://adb-5245952564735461.0.azuredatabricks.net/api/2.0/mlflow"),
        Err(PackageError::UnsupportedType)), "Type {} is not supported", "mlflow"
    );
}
#[test]
/// unsupported: MLflow model tracked in Azure ML (case sensitive)
fn unsupported_m_lflow_model_tracked_in_azure_ml_case_sensitive_() {
    assert!(
        matches!(Purl::from_str("pkg:mlflow/CreditFraud@3?repository_url=https://westus2.api.azureml.ms/mlflow/v1.0/subscriptions/a50f2011-fab8-4164-af23-c62881ef8c95/resourceGroups/TestResourceGroup/providers/Microsoft.MachineLearningServices/workspaces/TestWorkspace"),
        Err(PackageError::UnsupportedType)), "Type {} is not supported", "mlflow"
    );
}
#[test]
/// unsupported: MLflow model with unique identifiers
fn unsupported_m_lflow_model_with_unique_identifiers() {
    assert!(
        matches!(Purl::from_str("pkg:mlflow/trafficsigns@10?model_uuid=36233173b22f4c89b451f1228d700d49&run_id=410a3121-2709-4f88-98dd-dba0ef056b0a&repository_url=https://adb-5245952564735461.0.azuredatabricks.net/api/2.0/mlflow"),
        Err(PackageError::UnsupportedType)), "Type {} is not supported", "mlflow"
    );
}
#[test]
/// unsupported: composer names are not case sensitive
fn unsupported_composer_names_are_not_case_sensitive() {
    assert!(
        matches!(
            Purl::from_str("pkg:composer/Laravel/Laravel@5.5.0"),
            Err(PackageError::UnsupportedType)
        ),
        "Type {} is not supported",
        "composer"
    );
}