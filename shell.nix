{ pkgs ? import <nixpkgs> {} }:
let
  emacs = (pkgs.emacsPackagesNgGen pkgs.emacs).emacsWithPackages (epkgs:
    (with epkgs.melpaPackages; [ mkConfig epkgs.evil epkgs.agda2-mode]));

  agda = pkgs.agda.withPackages (p: with p; [ standard-library ]);

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
  ];
}
