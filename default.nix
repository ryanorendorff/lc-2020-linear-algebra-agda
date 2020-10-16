# This package can be called with the nixpkg function
# `agdaPackages.callPackage`, which is where the `standard-library` input comes
# from.

{ lib, stdenv, mkDerivation, standard-library, functional-linear-algebra }:

mkDerivation {
  version = "1.0";
  pname = "FormalizingLinearAlgebraAlgorithms";

  buildInputs = [ standard-library functional-linear-algebra ];

  src = lib.sourceFilesBySuffices ./. [
    ".agda"
    ".lagda"
    ".lagda.md"
    ".lagda.rst"
    ".lagda.tex"
    ".agda-lib"
  ];

  meta = with stdenv.lib; {
    homepage = "https://github.io/ryanorendorff/lc-2020-linear-algebra-agda";
    description = ''
      Formalizing Linear Algebra Algorithms using Dependently Typed Functional
      Programming
    '';
    license = licenses.bsd3;
    platforms = platforms.unix;
    maintainers = with maintainers; [ ryanorendorff ];
  };
}
