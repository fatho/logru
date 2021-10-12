{
  sources ? import ./nix/sources.nix,
  nixpkgs ? import sources.nixpkgs {},
}:
{
  logru = nixpkgs.callPackage (
    { bash, lib, nix-gitignore, rustPlatform }:
    rustPlatform.buildRustPackage {
      pname = "logru";
      version = "0.1.0";

      src =
        let
          # Potential extra things to remove
          extraFilter = path: type: true;
          # Gitignore + extras
          gitignore = ''
            ${builtins.readFile ./.gitignore}
            /.git
            /.github
            /nix

            /.envrc
            /.gitignore
            /rust-toolchain
            *.nix
            *.md
          '';
          gitignoreFilter = nix-gitignore.gitignoreFilterPure extraFilter gitignore ./.;
          blacklistedSrc = lib.cleanSourceWith {
            src = ./.;
            filter = gitignoreFilter;
          };
        in
          blacklistedSrc;

      cargoSha256 = "08fq0azc6wib6rqnxmm4r5pjqnx4pnww7lbhbc350gqh7g4jfyzp";

      meta = with lib; {
          description = "Logic programming in Rust";
          homepage = https://github.com/fatho/logru;
          license = licenses.mit;
          maintainers = [ "Fabian Thorand" ];
          platforms = platforms.all;
      };
    }
  ) {};
}
