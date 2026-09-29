{ pkgs ? import <nixpkgs> {} }:

pkgs.mkShell {
  packages = [
    pkgs.ocaml
    pkgs.ghc
    pkgs.dotnet-sdk
    pkgs.elmPackages.elm
    pkgs.polyml
  ];
}
