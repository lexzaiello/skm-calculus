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
      in with pkgs.python3Packages;
      let deps = [ regex jinja2 mistletoe toml fire beautifulsoup4 pygments ];
      in rec {
        packages.formatter = buildPythonApplication {
          name = "lean-format";
          src = lean-formatter;
          format = "pyproject";
          nativeBuildInputs = [ setuptools wheel ] ++ deps;
          propagatedBuildInputs = deps;
        };
        apps.format = let
          format_all = pkgs.writeShellScriptBin "format_all" ''
            find . -type f -name "*.lean" | while read -r file; do
              ${packages.formatter}/bin/format_lean $file
            done
          '';
        in {
          type = "app";
          program = "${format_all}/bin/format_all";
        };
        devShells.default = pkgs.mkShell {
          packages = with pkgs.python3Packages; [ packages.formatter ] ++ deps;
        };
      });
}
