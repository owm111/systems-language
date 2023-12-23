{
  description = "A compiler front end";

  outputs = { self, nixpkgs }: {

    lib = {
      pkgsForEach = nixpkgs: cfg: systems: attrs: let
        sys2attrset = system: {
          name = system;
          value = let
            cfg' = cfg // { inherit system; };
            pkgs = import nixpkgs cfg';
            apply = _: f: f pkgs system;
          in builtins.mapAttrs apply attrs;
        };
      in builtins.listToAttrs (map sys2attrset systems);

      defSystems = [ "x86_64-linux" ];
    };

    devShells = self.lib.pkgsForEach nixpkgs {} self.lib.defSystems {
      default = pkgs: _: pkgs.mkShell {
        buildInputs = [
          pkgs.alex
          pkgs.happy
          (pkgs.haskellPackages.ghcWithPackages (hpkgs: [
            hpkgs.containers
            hpkgs.mtl
          ]))
          pkgs.byacc
          pkgs.flex
          pkgs.clang
          pkgs.noweb
        ];
      };
    };

  };
}
