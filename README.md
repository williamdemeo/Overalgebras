Overalgebras
============

This repository contains a journal article as well as the GAP software that was
used for constructing new finite algebras by extending and expanding transitive
G-sets, as described in the paper.  

**Title:** [Expansions of finite algebras and their congruence lattices][]  
**Author:** William DeMeo [@williamdemeo](https://github.com/williamdemeo)  
**Journal:** *Algebra Universalis*  
**Year:** 2013  

**Abstract:** In this paper we present a novel approach to the construction of
new finite algebras and describe the congruence lattices of these
algebras. Given a finite algebra (B<sub>0</sub>, ...), let
B<sub>1</sub>, B<sub>2</sub>, ..., B<sub>K</sub>
be sets that either intersect B<sub>0</sub> or intersect each other at certain
points. We construct an  *overalgebra* (A, F<sub>A</sub>), by which we mean an expansion
of (B<sub>0</sub>, ...) with universe that is the union of the B<sub>i</sub>'s and 
a certain set F<sub>A</sub> of unary operations that includes mappings
e<sub>i</sub> satisfying e<sub>i</sub><sup>2</sup> = e<sub>i</sub> and
e<sub>i</sub>(A) = B<sub>i</sub>, for 0 <= i <= K.

We explore two such constructions and prove results about the shape of
the new congruence lattices Con (A, F<sub>A</sub>) that result. Thus, descriptions of
some new classes of finitely representable lattices is one contribution of this
paper. Another, perhaps more significant contribution is the announcement of a
novel approach to the discovery of new classes of representable lattices, the
full potential of which we have only begun to explore.

**BibTeX entry:**

    @article {DeMeo:2013,
        AUTHOR = {DeMeo, William},
         TITLE = {Expansions of finite algebras and their congruence lattices},
       JOURNAL = {Algebra Universalis},
      FJOURNAL = {Algebra Universalis},
        VOLUME = {69},
          YEAR = {2013},
        NUMBER = {3},
         PAGES = {257--278},
          ISSN = {0002-5240},
       MRCLASS = {08A30 (06B10 08A60)},
      MRNUMBER = {3041715},
    MRREVIEWER = {E. W. Kiss},
           DOI = {10.1007/s00012-013-0226-3},
           URL = {http://dx.doi.org/10.1007/s00012-013-0226-3},
    }


The published version of the paper is in the file [DeMeo-Expansions-AU-2013.pdf][],
and is also available at [springer.com][]. 

In the file [gap2uacalc.g][] is a GAP program that can be used on its own to convert GAP groups and G-sets into UACalc .ua files,
which can then be imported into the [Universal Algebra Calculator](http://uacalc.org).
See [universalalgebra.org][] for more information about [gap2uacalc.g][].

For questions, comments, or suggestions please [submit an issue][].

Thanks for your interest in this work!

[@williamdemeo](https://github.com/williamdemeo)

[DeMeo-Expansions-AU-2013.pdf]: https://github.com/williamdemeo/Overalgebras/raw/master/DeMeo-Expansions-AU-2013.pdf
[springer.com]: http://link.springer.com
[Expansions of finite algebras and their congruence lattices]: https://github.com/williamdemeo/Overalgebras/raw/master/DeMeo-Expansions-AU-2013.pdf
[universalalgebra.org]: http://universalalgebra.wordpress.org/documentation/gap/gap-and-uacalc/ 
[gap2uacalc.g]: https://github.com/williamdemeo/Overalgebras/blob/master/gap2uacalc.g
[submit an issue]: https://github.com/williamdemeo/Overalgebras/issues
