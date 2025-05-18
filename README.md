# compilation
Verified compilator for a small subset of C, generated with Rocq, fully specified and verified.

The first version will consider only variable assignement, with addition and multiplication, using (infinite) nat from Rocq. The goal is to proove that compilation preserves semantic, using a "small step semantic" defined for both the C subset and the assembly code.

The proof is inspired by the CompCert project : the assembly language used is an abstraction using just a pile that mimics the real behavior. Once the specification is proven on this version, an equivalence (a proof of simulation) is made between the "pile version" and a more sophisticated "multi register" version, and finally another equivalence with a "real machine assembly langage".

More features can be added to the C subset once the first proof is finished.
