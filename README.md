WASM Component Semver
=====================

[![Crates.io](https://img.shields.io/crates/v/wasm-component-semver.svg)](https://crates.io/crates/wasm-component-semver)
[![Documentation](https://docs.rs/wasm-component-semver/badge.svg)](https://docs.rs/wasm-component-semver)
![License](https://img.shields.io/crates/l/wasm-component-semver.svg)

Library for working with semantic versions using logic that is compatible with the WebAssembly Component Model
implementation in Wasmtime.

For the provided `VersionMap` type, key lookup logic follows the rules:

- For `major` versions > `0`: select the latest version matching `${major}.*.*`
- For `minor` versions > `0` (when `major` is `0`): select the latest version matching `0.${minor}.*`
- Otherwise (when `major` and `minor` are both `0`): select the latest version matching `0.0.${patch}`
- Pre-release versions always must have an exact match in the map

## Installation

```shell
cargo add wasm-component-semver
```
