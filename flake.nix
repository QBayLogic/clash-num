# SPDX-FileCopyrightText: 2025 Google LLC
#
# SPDX-License-Identifier: CC0-1.0
{
    description = "clash-num dev shell";
    inputs = {
        nixpkgs.url = "github:NixOS/nixpkgs/nixos-25.05";
        flake-utils.url = "github:numtide/flake-utils";
        rust-overlay.url = "github:oxalica/rust-overlay";
        crane.url = "github:ipetkov/crane";
    };
    outputs = { self, nixpkgs, flake-utils, rust-overlay, crane }:
        flake-utils.lib.eachDefaultSystem (system:
            let
                overlays = [ rust-overlay.overlays.default ];
                pkgs = import nixpkgs {
                    inherit system overlays;
                    config = {
                        allowUnfree = true;
                    };
                };
                rustToolchain = pkgs.rust-bin.nightly.latest.default.override {
                    extensions = [ "rustfmt" "clippy" "miri" "rust-src" ];
                };
                rustPackage = pkgs.rustPlatform.buildRustPackage {
                    pname = "clash-num";
                    version = "0.1.0";
                    src = "./.";
                    cargoLock.lockFile = "./Cargo.lock";
                };
            in {
                devShells.default = pkgs.mkShell {
                    packages = with pkgs; [
                        rustToolchain
                        cargo-tarpaulin
                    ];
                    RUST_BACKTRACE = 1;
                };

                defaultPackage = rustPackage;
            }
        );
}