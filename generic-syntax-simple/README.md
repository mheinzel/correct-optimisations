# generic-syntax-simple

Based on [gallais/generic-syntax](https://github.com/gallais/generic-syntax),
with some changes:

- reduced to core functionality I needed
- without sized types (these caused complications after recent changes to the Agda compiler)
- (soon) with support for co-de-Bruijn-based terms,
  as in Conor McBride's [Everybody's Got To Be Somewhere](https://arxiv.org/abs/1807.04085)

Developed on:

- Agda 2.6.2.2
- Agda's Standard Library 1.7.1
