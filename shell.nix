{ pkgs ? import <nixpkgs> {} }:
let
  emacsConfig = pkgs.writeText "default.el" ''
(require 'evil)
  (evil-mode 1)
(require 'agda2-mode)
'';

  mkEmacsConfig = pkgs.runCommand "default.el" {} ''
mkdir -p $out/share/emacs/site-lisp
cp ${emacsConfig} $out/share/emacs/site-lisp/default.el
'';

  emacs = (pkgs.emacsPackagesFor pkgs.emacs).emacsWithPackages (epkgs:
    (with epkgs.melpaPackages; [ epkgs.evil epkgs.agda2-mode mkEmacsConfig ]));


  agda = pkgs.agda.withPackages (p: [
    p.standard-library
  ]);
in

pkgs.stdenv.mkDerivation {
  name = "agda-env";
  buildInputs = [
    agda
    pkgs.texlive.combined.scheme-full
    pkgs.haskellPackages.lhs2tex
    pkgs.pandoc
    pkgs.open-sans
    emacs
  ];
}
