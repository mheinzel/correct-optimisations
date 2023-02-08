{ pkgs ? import <nixpkgs> {} }:
let
  emacs = (pkgs.emacsPackagesFor pkgs.emacs).emacsWithPackages (epkgs:
    (with epkgs.melpaPackages; [ mkConfig epkgs.evil epkgs.agda2-mode]));

  agda = pkgs.agda.withPackages (p: [
    p.standard-library
    (p.mkDerivation {
      pname = "generic-syntax";
      version = "0.2.1";

      src = ./generic-syntax;

      includePaths = [ "src" ];
      buildInputs = [ p.standard-library ];
      everythingFile = "src/Everything.agda";

      meta = {
        homepage = "https://github.com/gallais/generic-syntax";
        description = "A Scope-and-Type Safe Universe of Syntaxes with Binding, Their Semantics and Proofs ";
      };
    })
  ]);

  emacsConfig = pkgs.writeText "default.el" ''
(require 'evil)
  (evil-mode 1)
(require 'agda2-mode)
'';

  mkConfig = pkgs.runCommand "default.el" {} ''
mkdir -p $out/share/emacs/site-lisp
cp ${emacsConfig} $out/share/emacs/site-lisp/default.el
'';
in

pkgs.stdenv.mkDerivation {
  name = "agda-env";
  buildInputs = [
    emacs
    agda
    pkgs.texlive.combined.scheme-full
    pkgs.haskellPackages.lhs2tex
    pkgs.pandoc
    pkgs.open-sans
  ];
}
