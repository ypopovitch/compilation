# compilation
Formally-verified compiler for a small subset of C. The compiler itself and its specifications are expressed with Rocq Prover. The final compiler code is extracted to OCaml. The verification shows the absence of runtime error and the preservation of semantic.

The first version will consider only variable assignment, with addition and multiplication, using (infinite) nat type from Rocq. More features can be added to the C subset once the specification is proven.

The proof uses a "small step semantic" defined for both the C subset and the assembly code. The proof main idea is inspired by the CompCert project : the assembly language used is an abstraction based on a pile. Once the specification is proven on the "pile version", an equivalence (a proof of simulation) is made between the "pile version" and a more sophisticated "multi register" version, and finally another equivalence with a "real machine assembly langage".
