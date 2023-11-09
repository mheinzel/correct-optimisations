## Analysis and Transformation of Intrinsically Typed Syntax

My master's thesis at Utrecht University, including work leading up to it.
The result is also [preserved on the UU Theses Repository](https://studenttheses.uu.nl/handle/20.500.12932/44219).

- `src`: Agda code
- `project-report`: technical report on a first step, the implementation and correctness proof of *dead binding elimination*
  - submitted PDF only, source code is preserved on [a separate branch](https://github.com/mheinzel/correct-optimisations/tree/main/tyde22)
- `tyde22`: extended abstract and slides for [my talk at TyDe 2022](https://icfp22.sigplan.org/details/tyde-2022-papers/11/Provingly-Correct-Optimisations-on-Intrinsically-Typed-Expressions-Extended-Abstract)
- `thesis-proposal`: background, preliminary results and schedule
- `thesis`: main thesis document
- `thesis-defence`: slides for my defence

### Source code

Developed on:

- Agda 2.6.2.2
- Agda's Standard Library 1.7.1

The code in `src/Generic` is based on [gallais/generic-syntax](https://github.com/gallais/generic-syntax),
with some changes:

- reduced to core functionality I needed
- without sized types (these caused complications after recent changes to the Agda compiler)
- with basic support for co-de-Bruijn-based terms,
  as in Conor McBride's [Everybody's Got To Be Somewhere](https://arxiv.org/abs/1807.04085)
