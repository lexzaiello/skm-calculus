{
  description = "Lean 4 Example Project";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-24.05";
    flake-utils.url = "github:numtide/flake-utils";
    lean-formatter = {
      url = "github:leanprover-community/format_lean";
      flake = false;
    };
  };
  outputs = { self, nixpkgs, flake-utils, lean-formatter }:
    flake-utils.lib.eachDefaultSystem (system:
      let pkgs = import nixpkgs { inherit system; };
      in rec {
        packages.formatter = pkgs.python3Packages.buildPythonPackage {
          name = "lean-format";
          src = lean-formatter;
          propogatedBuildInputs = with pkgs.python312Packages; [
            jinja2
            regex
            mistletoe
            beautifulsoup4
          ];
        };
        devShells.default = pkgs.mkShell { packages = [ packages.formatter ]; };
      });
}
