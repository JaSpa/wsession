{
  inputs.flake-utils.url = github:numtide/flake-utils;
  inputs.agda-stdlib.url = github:agda/agda-stdlib;
  inputs.agda-stdlib.flake = false;

  outputs = {
    self,
    nixpkgs,
    flake-utils,
    agda-stdlib,
  }:
    flake-utils.lib.eachDefaultSystem (
      system: let
        pkgs = nixpkgs.legacyPackages.${system};
      in {
        formatter = pkgs.alejandra;
        packages = rec {
          agda = pkgs.agda.withPackages (p: [
            (p.standard-library.overrideAttrs (attrs: {
              version = "2.0-dev";
              src = agda-stdlib;
              # We skip building (that is checking of all modules) because it
              # takes quite long and only a subset is actually used.
              dontBuild = true;
            }))
          ]);
          default = pkgs.buildEnv {
            name = "wsessions-env";
            paths = with pkgs; [
              agda
              gnumake
              nano
            ];
          };
        };
      }
    );
}
