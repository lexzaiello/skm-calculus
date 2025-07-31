{
  description = "Lean 4 Example Project";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    haskellNix.url = "github:input-output-hk/haskell.nix";
  };
  outputs = { self, nixpkgs, flake-utils, haskellNix }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        overlays = [
          haskellNix.overlay
          (final: _prev: {
            
            # This overlay adds our project to pkgs
            skm-cli = final.haskell-nix.project' {
              src = ./cli;
              compiler-nix-name = "ghc983";
              # This is used by `nix develop .` to open a shell for use with
              # `cabal`, `hlint` and `haskell-language-server`
              shell.tools = {
                cabal = { };
                # hlint = {};
                haskell-language-server = {};
              };
              # Non-Haskell shell tools go here
              shell.buildInputs = with pkgs; [ nixpkgs-fmt ];
              # This adds `js-unknown-ghcjs-cabal` to the shell.
              # shell.crossPlatforms = p: [p.ghcjs];
            };
          })
        ];
        pkgs = import nixpkgs {
          inherit system overlays;
          inherit (haskellNix) config;
        };
        booktoml = ''
          [book]
          title = "The Dependently-Typed SK(M) Calculus"
          author = "Alexandra Zaldivar Aiello"

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
            find formal/SkLean -type f -name "*.lean" -not -path "formal/SkLean/tests/*" | while read -r file; do
              ${md}/bin/md < $file > $file.md
            done
            find . -type f -name "*.org" | while read -r file; do
              ${pkgs.pandoc}/bin/pandoc --lua-filter=${
                ./scripts/fixinlinelatexorg.lua
              } -s $file -o $file.md
            done
          '';
          installPhase = ''
            mkdir -p $out/
            find . -type f -name "*.md" | while read -r file; do
              mv $file $out
            done
          '';
        };
        flake = pkgs.skm-cli.flake {
          # This adds support for `nix build .#js-unknown-ghcjs:hello:exe:hello`
          # crossPlatforms = p: [p.ghcjs];
        };
      in flake // rec {
        packages.md = md;
        packages.book-md = book-md;
        packages.skm = flake.packages."skm:exe:skm";
        packages.book-site = let
          summarymd = ''
            # Summary

            [Introduction](./README.org.md)

            # Background
            - [Typed and Untyped Lambda Calculus](./Lc.lean.md)
            - [Strong Normalization](./SnLc.lean.md)
            - [SK Combinators](./SkRaw.lean.md)

            # Dependent Typing in SK
            - [Overview](./SkmOverview.lean.md)
            - [AST & Judgment Rules](./Ast3.lean.md)

            # Strong Normalization Proof
          '';
        in pkgs.stdenv.mkDerivation {
          name = "book-html";
          src = book-md;
          buildPhase = ''
            mkdir src
            mv *.md src/
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
        apps.skm = {
          type = "app";
          program = "${flake.packages."skm:exe:skm"}/bin/skm";
        };
        apps.serve-live = let
          serve-live = pkgs.writeShellScriptBin "serve-live" ''
            ${pkgs.watchexec}/bin/watchexec -e lean,md,nix,org --restart -- nix run .#book-serve
          '';
        in {
          type = "app";
          program = "${serve-live}/bin/serve-live";
        };
      });
}
