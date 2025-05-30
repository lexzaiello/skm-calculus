{
  description = "Lean 4 Example Project";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-24.05";
    flake-utils.url = "github:numtide/flake-utils";
  };
  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
        booktoml = ''
          [book]
          title = "Strong Normalization of the Dependently-Typed SK Combinators in Lean"

          [output.html]
          mathjax-support = true
          additional-js = ["highlight.js"]
        '';
        md = with pkgs.haskellPackages;
          pkgs.stdenv.mkDerivation {
            name = "md";
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
        book-md = pkgs.stdenv.mkDerivation {
          name = "book-md";
          src = ./.;
          buildPhase = ''
            find SkLean -type f -name "*.lean" | while read -r file; do
              echo $file
              ${md}/bin/md < $file > $file.md
            done
          '';
          installPhase = ''
            mkdir -p $out/
            find SkLean -type f -name "*.md" | while read -r file; do
              mv $file $out
            done
          '';
        };
      in rec {
        packages.md = md;
        packages.book-md = book-md;
        packages.book-site = let
          summarymd = ''
            # Summary

            [Introduction](./README.md)

            # Background
            - [Typed and Untyped Lambda Calculus](./Lc.lean.md)

            # Type Discipline
            - [Dependently-Typed SK Combinators: AST](./Ast.lean.md)
          '';
        in pkgs.stdenv.mkDerivation {
          name = "book-html";
          src = book-md;
          buildPhase = ''
            mkdir src
            mv *.md src/
            cp ${./README.md} src/README.md
            cp ${./scripts/highlight.js} highlight.js
            echo '${booktoml}' > book.toml
            echo '${summarymd}' > src/SUMMARY.md
            ${pkgs.mdbook}/bin/mdbook build
          '';
          installPhase = ''
            mkdir $out
            mv ./book/* $out
          '';
        };
        apps.book-serve = let
          serve-bin = pkgs.writeShellScriptBin "serve"
            "${pkgs.http-server}/bin/http-server ${packages.book-site} -c-1";
        in {
          name = "book-serve";
          type = "app";
          program = "${serve-bin}/bin/serve";
        };
        apps.serve-live = let
          serve-live = pkgs.writeShellScriptBin "serve-live" ''
            ${pkgs.watchexec}/bin/watchexec -e lean,md,nix --restart -- nix run .#book-serve
          '';
        in {
          type = "app";
          program = "${serve-live}/bin/serve-live";
        };
      });
}
