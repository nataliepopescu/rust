let
  nixpkgs = fetchTarball "https://github.com/NixOS/nixpkgs/tarball/nixos-25.11";
  pkgs = import nixpkgs { config = {}; overlays = []; };
in

pkgs.mkShellNoCC {
  packages = with pkgs; [
    python3
    rustup
    gcc
    libllvm
  ];

  shellHook = ''
    # export LD_LIBRARY_PATH="/nix/store/qksd2mz9f5iasbsh398akdb58fx9kx6d-gcc-13.2.0-lib/lib/"
    # export LD_LIBRARY_PATH="$(rustc +nightly-2026-01-13-x86_64-unknown-linux-gnu --print target-libdir):$LD_LIBRARY_PATH"
    export LD_LIBRARY_PATH="${pkgs.lib.makeLibraryPath [ pkgs.stdenv.cc.cc.lib ]}:$(rustc +nightly-2026-01-13-x86_64-unknown-linux-gnu --print target-libdir):$LD_LIBRARY_PATH"
  '';
}
