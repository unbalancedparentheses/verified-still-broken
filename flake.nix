{
  description = "Verified, still broken — formal-verification gaps demonstrated in Lean 4";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
        lean = pkgs.lean4;
      in {
        devShells.default = pkgs.mkShell {
          packages = [ lean ];
          shellHook = ''
            echo "Lean toolchain: $(lean --version)"
          '';
        };

        # `nix run` checks every example compiles (C2 is expected to emit
        # axiom/sorry diagnostics — that is the point of that example).
        apps.default = {
          type = "app";
          program = toString (pkgs.writeShellScript "check-all" ''
            set -e
            for f in ${self}/Examples/*.lean; do
              echo "== checking $f =="
              ${lean}/bin/lean "$f"
            done
          '');
        };
      });
}
