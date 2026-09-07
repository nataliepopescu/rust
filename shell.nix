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
    libxml2
    zlib
  ];

  shellHook = ''
    export LD_LIBRARY_PATH="${pkgs.lib.makeLibraryPath [ pkgs.stdenv.cc.cc.lib pkgs.zlib ]}:$(rustc +nightly-2026-01-13-x86_64-unknown-linux-gnu --print target-libdir):$LD_LIBRARY_PATH"
    export LIBRARY_PATH="${pkgs.lib.makeLibraryPath [ pkgs.libxml2 ]}:$LIBRARY_PATH"
  '';
}
