let
  pkgs = import ./nixpkgs.nix;

  # Convenient for using the existing .gitignore to automatically untrack
  # unwanted files in src/.
  inherit (import (pkgs.fetchFromGitHub {
    owner = "hercules-ci";
    repo = "gitignore";
    rev = "c4662e662462e7bf3c2a968483478a665d00e717";
    sha256 = "1npnx0h6bd0d7ql93ka7azhj40zgjp815fw2r6smg8ch9p7mzdlx";
  }) { inherit (pkgs) lib; })
    gitignoreSource;

  texlive = pkgs.texlive.combine {
    inherit (pkgs.texlive)
      scheme-small fontspec pgfopts epsdice beamer beamertheme-metropolis;
  };

  fonts = pkgs.makeFontsConf {
    fontDirectories = with pkgs; [ fira fira-mono iosevka ];
  };

in pkgs.stdenv.mkDerivation {
  name = "FormalizingLinearAlgebraAlgorithmsPresentation";
  src = gitignoreSource ./src;

  phases = [ "unpackPhase" "buildPhase" ];

  buildInputs = with pkgs; [ texlive pandoc ];

  FONTCONFIG_FILE = "${fonts}";

  buildPhase = ''
    mkdir $out
    pandoc FormalizingLinearAlgebraAlgorithms.lagda.md \
           -o $out/FormalizingLinearAlgebraAlgorithms.pdf \
           -t beamer \
           --slide-level=2 \
           --pdf-engine=xelatex
  '';
}
