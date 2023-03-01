## Anonymous supplement for Session Types without Linearity

This supplement contains the literate Agda code that is shown in the paper.
It consists of the files below. The code requires installing the latest (unreleased) version of the Agda standard library from
https://github.com/agda/agda-stdlib
The material for sections 2-4 can be made to work with the current release (1.7.2) of the standard library without much effort. 

### Channels.lagda

Postulates for the channel API.

### Utils.lagda

Implementation of the isomorphism between `Vec A n` and `Fin n -> A`.

### ST-finite-nonbranching.lagda

Contains the material presented in Section 2 and (counter the name) the material from Section 3 on branching session types. Imports Channels, Utils.

### ST-recursive.lagda

The material presentation in Section 4 on session types with recursion.
Imports Channels, Utils.

### ST-monadic.lagda

The monadic interface presented in Section 5.
Imports Channels.

### ST-indexed-contextfree.lagda

Context-free session types as presented in Section 6. 
Imports Channels, Utils.

### ST-multichannel.lagda

Multichannel session types according to Section 7.
No local imports.
