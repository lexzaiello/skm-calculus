{
  description = "Lean 4 Example Project";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-24.05";
    flake-utils.url = "github:numtide/flake-utils";
  };
  outputs = { self, nixpkgs, flake-utils, lean-formatter }:
    flake-utils.lib.eachDefaultSystem (system:
      let pkgs = import nixpkgs { inherit system; };
      in rec {
        packages.md = with pkgs.haskellPackages;
          pkgs.stdenv.mkDerivation {
            buildInputs = [ ghc ];
            src = ./scripts;
            buildPhase = ''
              ghc ToMarkdown.hs -o md
            '';
            installPhase = ''
              mkdir -p $out/bin
              cp md $out/bin
            '';
          };
        packages.book-md = pkgs.stdenv.mkDerivation {
          src = ./.;
          buildPhase = ''
            find . -type f -name "*.lean" | while read -r file; do
              ${packages.md}/bin/md < $file > $file.md
            done
          '';
          installPhase = ''
            
          '';
        };
      });
}
