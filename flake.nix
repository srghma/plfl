{
  description = "Lean 4 Example Project";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-24.05";
    flake-parts.url = "github:hercules-ci/flake-parts";
    lean4-nix.url = "github:lenianiva/lean4-nix";
  };

  outputs =
    inputs@{
      nixpkgs,
      flake-parts,
      lean4-nix,
      ...
    }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      systems = [
        "aarch64-darwin"
        "aarch64-linux"
        "x86_64-darwin"
        "x86_64-linux"
      ];

      perSystem =
        {
          system,
          pkgs,
          ...
        }:
        {
          _module.args.pkgs = import nixpkgs {
            inherit system;
            overlays = [ (lean4-nix.readToolchainFile ./lean-toolchain) ];
          };

          packages.default =
            ((lean4-nix.lake { inherit pkgs; }).mkPackage {
              src = ./.;
              roots = [ "Example" ];
              deps = with pkgs.lean; [
                Init
                Std
                Lean
              ];
            }).executable;

          devShells.default = pkgs.mkShell {
            MATHLIB_NO_CACHE_ON_UPDATE = "true";
            packages = with pkgs.lean; [
              lean
              lean-all
            ];
          };
        };
    };
}
