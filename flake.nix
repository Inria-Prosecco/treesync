{
  inputs = {
    nixpkgs.url = "nixpkgs";

    fstar-src = {
      url = "github:FStarLang/FStar";
      flake = false;
    };

    everest = {
      url = github:project-everest/everest-nix?dir=projects;
      inputs.nixpkgs.follows = "nixpkgs";
      inputs.fstar-src.follows = "fstar-src";
    };
  };

  outputs = {self, nixpkgs, fstar-src, everest}:
  let
    system = "x86_64-linux";
    pkgs = import nixpkgs { inherit system; };
    z3 = everest.packages.${system}.z3;
    fstar = everest.packages.${system}.fstar;
  in {
    devShells.${system}.default = pkgs.mkShell {
      packages = [
        fstar z3
      ] ++ (with pkgs.ocaml-ng.ocamlPackages_4_12; [
        ocaml dune_2 findlib
        # fstarlib dependencies
        batteries stdint zarith ppx_deriving_yojson
      ]);
    };
  };
}
