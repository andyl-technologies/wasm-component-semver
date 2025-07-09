{
  pkgs,
  config,
  lib,
  ...
}:

{
  packages = with pkgs; [
    cargo-nextest
    cargo-watch
    git
  ];

  languages.rust.enable = true;

  processes = lib.optionalAttrs (!config.devenv.isTesting) {
    cargo-watch.exec = "cargo-watch";
  };

  enterTest = ''
    set -e
    cargo fmt --check --all
    cargo check --all-targets
    cargo nextest run --all-features
    cargo test --doc
  '';

  git-hooks.hooks.actionlint.enable = true;
  git-hooks.hooks.nixfmt-rfc-style.enable = true;
}
