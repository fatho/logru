let
  sources = import ./nix/sources.nix;
  mozilla = import (sources.nixpkgs-mozilla + "/rust-overlay.nix");
  nixpkgs = import sources.nixpkgs {
    overlays = [mozilla];
  };
  channel = nixpkgs.rustChannelOf { rustToolchain = ./rust-toolchain; };
in
  nixpkgs.mkShell {
    name = "logru-dev";

    nativeBuildInputs = with nixpkgs; [
      # Rust core
      channel.rust

      # Toolchain
      lld_13
      lldb_13
      pkg-config

      # Neat helper tools
      cargo-audit
      cargo-criterion
      cargo-deny
      cargo-edit
      cargo-flamegraph
      gnuplot  # for criterion

      # Nix tools
      niv
    ];

    # Always enable rust backtraces in development shell
    RUST_BACKTRACE = "1";

    # Provide sources for rust-analyzer, because nixpkgs rustc doesn't include them in the sysroot
    RUST_SRC_PATH = "${channel.rust-src}/lib/rustlib/src/rust/library";
  }
