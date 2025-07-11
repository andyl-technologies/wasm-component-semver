//! A specialized map for semantic versions with alternate version lookup support.
//!
//! This module best approximates the behavior of WASM component loading in `wasmtime`,
//! such as in `wasmtime::component::Linker`.
//!
//! This module provides `VersionMap<T>`, which stores values indexed by semantic versions
//! and supports fallback lookups through version alternates (e.g., 1.2.3 can be found
//! via 1.0.0 if it's the latest patch for major version 1).

use derivative::Derivative;
use semver::Version;
use std::borrow::Borrow;
use std::collections::{BTreeMap, BTreeSet, HashMap};
#[cfg(feature = "borsh")]
use std::io::{Read, Write};

/// A map that stores values indexed by semantic versions with support for alternate lookups.
///
/// The `VersionMap` maintains a primary mapping from versions to values, and a secondary
/// mapping that groups versions by their "alternate" keys for fallback lookups.
///
/// # Alternate Lookup Logic
///
/// - For major versions > 0: alternate is `major.*.*`
/// - For minor versions > 0 (when major is 0): alternate is `0.minor.*`
/// - Otherwise: alternate is `0.0.patch`
/// - Pre-release versions have no alternates
///
/// # Example
///
/// ```rust
/// use semver::Version;
/// # use wasm_component_semver::VersionMap;
///
/// let mut map = VersionMap::new();
/// map.insert(Version::new(1, 0, 1), "v1.0.1");
/// map.insert(Version::new(1, 2, 0), "v1.2.0");
///
/// // Exact lookups
/// assert_eq!(map.get_exact(&Version::new(1, 0, 1)), Some(&"v1.0.1"));
///
/// // Alternate lookups (finds latest patch for major version 1)
/// assert_eq!(map.get(&Version::new(1, 0, 0)), Some(&"v1.2.0"));
/// ```
#[derive(Clone, Derivative, Debug)]
#[derivative(Default(bound = ""))]
pub struct VersionMap<T> {
    /// Primary storage mapping versions to values
    versions: BTreeMap<WrappedVersion, T>,
    /// Secondary mapping for alternate version lookups
    alternates: HashMap<Version, BTreeSet<WrappedVersion>>,
}

impl<T> VersionMap<T> {
    /// Creates a new empty `VersionMap`.
    pub fn new() -> Self {
        Self {
            versions: BTreeMap::new(),
            alternates: HashMap::new(),
        }
    }

    #[cfg(any(feature = "borsh", feature = "serde"))]
    fn from_versions(versions: BTreeMap<WrappedVersion, T>) -> Self {
        let mut alternates: HashMap<Version, BTreeSet<WrappedVersion>> = HashMap::new();

        for version in versions.keys() {
            if let Some(alternate) = version_alternate(&version.inner) {
                alternates
                    .entry(alternate)
                    .or_default()
                    .insert(version.clone());
            }
        }

        Self {
            versions,
            alternates,
        }
    }

    /// Attempts to insert a version-value pair, returning an error if the version already exists.
    pub fn try_insert(&mut self, version: Version, value: T) -> Result<(), (Version, T)> {
        let version: WrappedVersion = version.into();

        if self.versions.contains_key(&version) {
            return Err((version.into(), value));
        }

        if let Some(alternate) = version_alternate(&version.inner) {
            self.alternates
                .entry(alternate)
                .or_default()
                .insert(version.clone());
        }

        self.versions.insert(version, value);

        Ok(())
    }

    /// Inserts a version-value pair, returning the previous value if the version existed.
    ///
    /// Updates the alternates mapping appropriately.
    pub fn insert(&mut self, version: Version, value: T) -> Option<T> {
        let version: WrappedVersion = version.into();

        if let Some(alternate) = version_alternate(&version.inner) {
            self.alternates
                .entry(alternate)
                .or_default()
                .insert(version.clone());
        }

        self.versions.insert(version, value)
    }

    /// Gets a value by version, using alternate lookup if exact match is not found.
    /// # Examples
    ///
    /// ```rust
    /// use semver::Version;
    /// # use wasm_component_semver::VersionMap;
    ///
    /// let mut map = VersionMap::new();
    /// map.insert(Version::new(0, 0, 9), "v0.0.9");
    /// map.insert(Version::new(0, 1, 1), "v0.1.1");
    /// map.insert(Version::new(1, 2, 1), "v1.2.1");
    ///
    /// // Get latest patch
    /// assert_eq!(map.get(&Version::new(0, 0, 9)), Some(&"v0.0.9"));
    ///
    /// // Get latest minor
    /// assert_eq!(map.get(&Version::new(0, 1, 0)), Some(&"v0.1.1"));
    ///
    /// // Get latest major
    /// assert_eq!(map.get(&Version::new(1, 0, 0)), Some(&"v1.2.1"));
    pub fn get(&self, version: &Version) -> Option<&T> {
        if version.build.is_empty() {
            let maybe_value = version_alternate(version)
                .as_ref()
                .and_then(|alternate| self.alternates.get(alternate))
                .and_then(|version_set| version_set.last())
                .and_then(|version| self.versions.get(version));

            if maybe_value.is_some() {
                return maybe_value;
            }
        }

        self.versions.get(version)
    }

    /// Like `get`, but returns the resolved version and value as a tuple.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use semver::Version;
    /// # use wasm_component_semver::VersionMap;
    ///
    /// let mut map = VersionMap::new();
    /// map.insert(Version::new(0, 0, 9), "v0.0.9");
    /// map.insert(Version::new(0, 1, 1), "v0.1.1");
    /// map.insert(Version::new(1, 2, 1), "v1.2.1");
    ///
    /// // Get latest patch
    /// assert_eq!(map.get_version(&Version::new(0, 0, 9)), Some((&Version::new(0, 0, 9), &"v0.0.9")));
    ///
    /// // Get latest minor
    /// assert_eq!(map.get_version(&Version::new(0, 1, 0)), Some((&Version::new(0, 1, 1), &"v0.1.1")));
    ///
    /// // Get latest major
    /// assert_eq!(map.get_version(&Version::new(1, 0, 0)), Some((&Version::new(1, 2, 1), &"v1.2.1")));
    pub fn get_version(&self, version: &Version) -> Option<(&Version, &T)> {
        if version.build.is_empty() {
            let maybe_key_value = version_alternate(version)
                .as_ref()
                .and_then(|alternate| self.alternates.get(alternate))
                .and_then(|version_set| version_set.last())
                .and_then(|version| self.versions.get_key_value(version));

            if maybe_key_value.is_some() {
                return maybe_key_value.map(|(k, v)| (k.borrow(), v));
            }
        }

        self.versions
            .get_key_value(version)
            .map(|(k, v)| (k.borrow(), v))
    }

    /// Gets a value by version or returns the latest version if no specific version is provided.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use semver::Version;
    /// # use wasm_component_semver::VersionMap;
    ///
    /// let mut map = VersionMap::new();
    /// map.insert(Version::new(0, 0, 9), "v0.0.9");
    /// map.insert(Version::new(0, 1, 0), "v0.1.0");
    /// map.insert(Version::new(0, 1, 1), "v0.1.1");
    /// map.insert(Version::new(0, 5, 1), "v0.5.1");
    /// map.insert(Version::new(1, 0, 0), "v1.0.0");
    /// map.insert(Version::new(1, 2, 0), "v1.2.0");
    ///
    /// // Get latest patch
    /// assert_eq!(map.get_or_latest(Some(&Version::new(0, 0, 9))), Some(&"v0.0.9"));
    ///
    /// // Get latest minor
    /// assert_eq!(map.get_or_latest(Some(&Version::new(0, 1, 0))), Some(&"v0.1.1"));
    ///
    /// // Get latest major
    /// assert_eq!(map.get_or_latest(Some(&Version::new(1, 0, 0))), Some(&"v1.2.0"));
    ///
    /// // Get the latest version
    /// assert_eq!(map.get_or_latest(None), Some(&"v1.2.0"));
    /// ```
    pub fn get_or_latest(&self, version: Option<&Version>) -> Option<&T> {
        match version {
            Some(v) => self.get(v),
            None => self.get_latest().map(|(_, value)| value),
        }
    }

    /// Gets a value by version or returns the latest version and its associated value
    /// if no specific version is provided.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use semver::Version;
    /// # use wasm_component_semver::VersionMap;
    ///
    /// let mut map = VersionMap::new();
    /// map.insert(Version::new(0, 0, 9), "v0.0.9");
    /// map.insert(Version::new(0, 1, 0), "v0.1.0");
    /// map.insert(Version::new(0, 1, 1), "v0.1.1");
    /// map.insert(Version::new(0, 5, 1), "v0.5.1");
    /// map.insert(Version::new(1, 0, 0), "v1.0.0");
    /// map.insert(Version::new(1, 2, 0), "v1.2.0");
    ///
    /// // Get latest patch
    /// assert_eq!(map.get_or_latest_version(Some(&Version::new(0, 0, 9))), Some((&Version::new(0, 0, 9), &"v0.0.9")));
    ///
    /// // Get latest minor
    /// assert_eq!(map.get_or_latest_version(Some(&Version::new(0, 1, 0))), Some((&Version::new(0, 1, 1), &"v0.1.1")));
    ///
    /// // Get latest major
    /// assert_eq!(map.get_or_latest_version(Some(&Version::new(1, 0, 0))), Some((&Version::new(1, 2, 0), &"v1.2.0")));
    ///
    /// // Get the latest version
    /// assert_eq!(map.get_or_latest_version(None), Some((&Version::new(1, 2, 0), &"v1.2.0")));
    /// ```
    pub fn get_or_latest_version(&self, version: Option<&Version>) -> Option<(&Version, &T)> {
        match version {
            Some(v) => self.get_version(v),
            None => self.get_latest(),
        }
    }

    /// Returns the latest version and its associated value.
    pub fn get_latest(&self) -> Option<(&Version, &T)> {
        self.versions.last_key_value().map(|(k, v)| (k.borrow(), v))
    }

    /// Gets a value by exact version match only, without alternate lookup.
    pub fn get_exact(&self, version: &Version) -> Option<&T> {
        self.versions.get(version)
    }

    pub fn remove(&mut self, version: &Version) -> Option<T> {
        if let Some(alternate) = version_alternate(version) {
            if let Some(set) = self.alternates.get_mut(&alternate) {
                set.remove(version);
                if set.is_empty() {
                    self.alternates.remove(&alternate);
                }
            }
        }

        self.versions.remove(version)
    }
}

#[cfg(feature = "borsh")]
impl<T: borsh::BorshSerialize> borsh::BorshSerialize for VersionMap<T> {
    fn serialize<W: Write>(&self, writer: &mut W) -> std::io::Result<()> {
        self.versions.serialize(writer)
    }
}

#[cfg(feature = "borsh")]
impl<T: borsh::BorshDeserialize> borsh::BorshDeserialize for VersionMap<T> {
    fn deserialize_reader<R: Read>(reader: &mut R) -> std::io::Result<Self> {
        let versions: BTreeMap<WrappedVersion, T> =
            borsh::BorshDeserialize::deserialize_reader(reader)?;
        Ok(Self::from_versions(versions))
    }
}

#[cfg(feature = "serde")]
impl<T: serde::Serialize> serde::Serialize for VersionMap<T> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        self.versions.serialize(serializer)
    }
}

#[cfg(feature = "serde")]
impl<'de, T: serde::Deserialize<'de>> serde::Deserialize<'de> for VersionMap<T> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let versions: BTreeMap<WrappedVersion, T> = serde::Deserialize::deserialize(deserializer)?;
        Ok(Self::from_versions(versions))
    }
}

/// Computes the alternate version key for fallback lookups.
///
/// This function implements the alternate lookup logic:
/// - Pre-release versions return `None` (no alternates)
/// - Major versions > 0: return `major.0.0`
/// - Minor versions > 0 (when major is 0): return `0.minor.0`
/// - Otherwise: return `0.0.patch`
fn version_alternate(version: &Version) -> Option<Version> {
    // Pre-release versions don't have alternates
    if !version.pre.is_empty() {
        None
    } else if version.major > 0 {
        Some(Version::new(version.major, 0, 0))
    } else if version.minor > 0 {
        Some(Version::new(0, version.minor, 0))
    } else {
        Some(Version::new(0, 0, version.patch))
    }
}

#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
#[repr(transparent)]
struct WrappedVersion {
    inner: Version,
}

impl Borrow<Version> for WrappedVersion {
    fn borrow(&self) -> &Version {
        &self.inner
    }
}

impl From<Version> for WrappedVersion {
    fn from(version: Version) -> Self {
        Self { inner: version }
    }
}

impl From<WrappedVersion> for Version {
    fn from(wrapped: WrappedVersion) -> Self {
        wrapped.inner
    }
}

#[cfg(feature = "borsh")]
impl borsh::BorshSerialize for WrappedVersion {
    fn serialize<W: Write>(&self, writer: &mut W) -> std::io::Result<()> {
        let s = self.inner.to_string();
        borsh::BorshSerialize::serialize(&s, writer)
    }
}

#[cfg(feature = "borsh")]
impl borsh::BorshDeserialize for WrappedVersion {
    fn deserialize_reader<R: Read>(reader: &mut R) -> std::io::Result<Self> {
        let s: String = borsh::BorshDeserialize::deserialize_reader(reader)?;

        let version = Version::parse(&s).map_err(|_| {
            std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                "Failed to parse version from string",
            )
        })?;

        Ok(Self { inner: version })
    }
}

#[cfg(feature = "serde")]
impl serde::Serialize for WrappedVersion {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        self.inner.serialize(serializer)
    }
}

#[cfg(feature = "serde")]
impl<'de> serde::Deserialize<'de> for WrappedVersion {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        Ok(Self {
            inner: serde::Deserialize::deserialize(deserializer)?,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use semver::Version;

    #[test]
    fn test_version_map_basic_operations() {
        let mut map = VersionMap::new();

        let version0 = Version::new(0, 4, 2);
        let version1 = Version::new(1, 0, 0);
        let version2 = Version::new(1, 0, 1);
        let version3 = Version::new(2, 0, 0);

        // Test insertions
        assert!(map.try_insert(version0.clone(), "value0").is_ok());
        assert!(map.try_insert(version1.clone(), "value1").is_ok());
        assert!(map.try_insert(version2.clone(), "value2").is_ok());
        assert!(map.try_insert(version3.clone(), "value3").is_ok());

        // Test duplicate insertion
        assert!(map.try_insert(version1.clone(), "duplicate").is_err());
    }

    #[test]
    fn test_version_map_alternate_zero() {
        let mut map = VersionMap::new();

        let version0 = Version::new(0, 0, 3);
        let version1 = Version::new(0, 3, 3);

        map.try_insert(version0.clone(), "value0").unwrap();
        map.try_insert(version1.clone(), "value1").unwrap();

        assert_eq!(map.get_version(&Version::new(0, 0, 1)), None);

        assert_eq!(
            map.get_version(&Version::new(0, 0, 3)),
            Some((&version0, &"value0"))
        );

        assert_eq!(
            map.get_version(&Version::new(0, 3, 0)),
            Some((&version1, &"value1"))
        );
    }

    #[test]
    fn test_version_map_alternate_lookups() {
        let mut map = VersionMap::new();

        let version0 = Version::new(0, 4, 2);
        let version1 = Version::new(1, 0, 0);
        let version2 = Version::new(1, 0, 1);
        let version3 = Version::new(2, 0, 0);

        map.try_insert(version0.clone(), "value0").unwrap();
        map.try_insert(version1.clone(), "value1").unwrap();
        map.try_insert(version2.clone(), "value2").unwrap();
        map.try_insert(version3.clone(), "value3").unwrap();

        // Test exact matches
        assert_eq!(map.get(&version0), Some(&"value0"));
        assert_eq!(map.get(&version2), Some(&"value2"));
        assert_eq!(map.get(&version3), Some(&"value3"));

        // Test alternate matches (should get latest in group)
        assert_eq!(map.get(&version1), Some(&"value2")); // 1.0.0 -> latest in 1.x.x group
        assert_eq!(map.get(&Version::new(0, 4, 1)), Some(&"value0")); // 0.4.1 -> latest in 0.4.x group
        assert_eq!(map.get(&Version::new(1, 1, 0)), Some(&"value2")); // 1.1.0 -> latest in 1.x.x group
        assert_eq!(map.get(&Version::new(2, 0, 4)), Some(&"value3")); // 2.0.4 -> latest in 2.x.x group

        // Test alternate matches with get_version
        assert_eq!(map.get_version(&version1), Some((&version2, &"value2"))); // 1.0.0 -> latest in 1.x.x group
        assert_eq!(
            map.get_version(&Version::new(0, 4, 1)),
            Some((&version0, &"value0"))
        ); // 0.4.1 -> latest in 0.4.x group
        assert_eq!(
            map.get_version(&Version::new(1, 1, 0)),
            Some((&version2, &"value2"))
        ); // 1.1.0 -> latest in 1.x.x group
        assert_eq!(
            map.get_version(&Version::new(2, 0, 4)),
            Some((&version3, &"value3"))
        ); // 2.0.4 -> latest in 2.x.x group

        // Test non-existent versions
        assert_eq!(map.get(&Version::new(0, 1, 0)), None);
        assert_eq!(map.get(&Version::new(3, 0, 0)), None);

        // Test exact lookups
        assert_eq!(map.get_exact(&version1), Some(&"value1"));
        assert_eq!(map.get_exact(&Version::new(1, 1, 0)), None); // No exact match
    }

    #[test]
    fn test_version_map_latest_operations() {
        let mut map = VersionMap::new();

        assert_eq!(map.get_latest(), None);
        assert_eq!(map.get_or_latest(None), None);

        map.insert(Version::new(1, 0, 0), "v1.0.0");
        map.insert(Version::new(2, 0, 0), "v2.0.0");
        map.insert(Version::new(0, 1, 0), "v0.1.0");

        assert_eq!(map.get_latest(), Some((&Version::new(2, 0, 0), &"v2.0.0")));
        assert_eq!(map.get_or_latest(None), Some(&"v2.0.0"));
        assert_eq!(
            map.get_or_latest(Some(&Version::new(1, 0, 0))),
            Some(&"v1.0.0")
        );
    }

    #[test]
    fn test_version_map_insert_and_removal() {
        let mut map = VersionMap::new();

        let v1 = Version::new(1, 0, 0);
        let v2 = Version::new(1, 0, 1);

        map.insert(v1.clone(), "v1");
        map.insert(v2.clone(), "v2");

        assert_eq!(map.remove(&v1), Some("v1"));
        assert_eq!(map.remove(&v1), None); // Already removed
    }

    #[test]
    fn test_version_alternate_function() {
        // Pre-release versions have no alternates
        let pre = Version::parse("1.0.0-alpha").unwrap();
        assert_eq!(version_alternate(&pre), None);

        // Major versions > 0
        assert_eq!(
            version_alternate(&Version::new(1, 2, 3)),
            Some(Version::new(1, 0, 0))
        );
        assert_eq!(
            version_alternate(&Version::new(2, 5, 1)),
            Some(Version::new(2, 0, 0))
        );

        // Minor versions > 0 (when major is 0)
        assert_eq!(
            version_alternate(&Version::new(0, 1, 5)),
            Some(Version::new(0, 1, 0))
        );
        assert_eq!(
            version_alternate(&Version::new(0, 3, 2)),
            Some(Version::new(0, 3, 0))
        );

        // Patch versions (when major and minor are 0)
        assert_eq!(
            version_alternate(&Version::new(0, 0, 1)),
            Some(Version::new(0, 0, 1))
        );
        assert_eq!(
            version_alternate(&Version::new(0, 0, 5)),
            Some(Version::new(0, 0, 5))
        );
    }

    #[test]
    #[cfg(feature = "borsh")]
    fn test_borsh_serialize_deserialize() {
        use borsh::{BorshDeserialize, BorshSerialize};

        let mut map = VersionMap::new();
        map.insert(Version::new(1, 0, 0), "v1.0.0");
        map.insert(Version::new(2, 0, 0), "v2.0.0");

        // Serialize
        let mut buffer = Vec::new();
        map.serialize(&mut buffer).unwrap();

        // Deserialize
        let deserialized_map: VersionMap<String> =
            BorshDeserialize::deserialize_reader(&mut &buffer[..]).unwrap();

        assert_eq!(
            deserialized_map.get(&Version::new(1, 0, 0)),
            Some(&"v1.0.0".to_string())
        );

        assert_eq!(
            deserialized_map.get(&Version::new(2, 0, 0)),
            Some(&"v2.0.0".to_string())
        );
    }

    #[test]
    #[cfg(feature = "serde")]
    fn test_serde_serialize_deserialize() {
        let mut map = VersionMap::new();
        map.insert(Version::new(1, 0, 0), "v1.0.0");
        map.insert(Version::new(2, 0, 0), "v2.0.0");

        // Serialize
        let serialized = serde_json::to_string(&map).unwrap();

        // Deserialize
        let deserialized_map: VersionMap<String> = serde_json::from_str(&serialized).unwrap();

        assert_eq!(
            deserialized_map.get(&Version::new(1, 0, 0)),
            Some(&"v1.0.0".to_string())
        );

        assert_eq!(
            deserialized_map.get(&Version::new(2, 0, 0)),
            Some(&"v2.0.0".to_string())
        );
    }
}
