{
  description = "Lean 4 Example Project";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };
  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
        booktoml = ''
          [book]
          title = "Towards a Dependently-Typed Combinatory Calculus"
          author = "Alexandra Zaldivar Aiello"

          [output.html]
          mathjax-support = false
          additional-js = ["highlight.js", "mathjaxconfig.js"]
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
              ${pkgs.pandoc}/bin/pandoc --lua-filter=${./scripts/fixinlinelatexorg.lua} -s $file -o $file.md
            done
          '';
          installPhase = ''
            mkdir -p $out/
            find . -type f -name "*.md" | while read -r file; do
              mv $file $out
            done
          '';
        };
        skm-cli = pkgs.haskellPackages.developPackage {
          root = ./cli;
        };
      in rec {
        packages.md = md;
        packages.book-md = book-md;
        packages.skm = skm-cli;
        packages.book-site = let
          summarymd = ''
            # Summary

            [Introduction](./README.org.md)

            # Introducing SKΠ
            - [Intro](./Intro.lean.md)
            - [Ast](./Ast.lean.md)
            - [Evaluation & Typing Rules](./Rules.lean.md)
          '';
        in pkgs.stdenv.mkDerivation {
          name = "book-html";
          src = book-md;
          buildPhase = ''
            mkdir src
            mv *.md src/
            cp ${./scripts/highlight.js} highlight.js
            cp ${./scripts/mathjaxconfig.js} mathjaxconfig.js
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
        devShells.default = with pkgs.haskellPackages; pkgs.mkShell {
          nativeBuildInputs = [ ghc hpack haskell-language-server cabal-install pkgs.elan ];
        };
        apps.skm = {
          type = "app";
          program = "${skm-cli}/bin/skm";
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
