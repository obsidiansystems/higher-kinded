{ config, ... }:

let nix-thunk = config.importing.nix-thunk;
    deps = with nix-thunk; mapSubdirectories thunkSource ./deps;

in {
  name = "higher-kinded";
  src = ./.;
  compiler-nix-name = "ghc912";

  shell = {
    packages = ps: with ps; [
      higher-kinded
      higher-kinded-data
      higher-kinded-instance-beam
      higher-kinded-types
    ];
  };
}
