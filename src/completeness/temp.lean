1. Let CGψ ∈ sf, and tf be some world such that sf ∼f CG tf.
2. This proof is by induction on the size of G.
3. Base case: G = ∅. Proof by contradiction, from 1, because there cannot be a path sf ∼f CG tf.
4. Inductive step : G ≠ ∅. Inductive hypothesis for G ≠ ∅: ∀ uf, C G ψ ∈ uf → uf ∼f CG tf → (Mf, tf ⊨ ψ)
4.1 ∀ tf, sf ∼fi tf → ψ ∈ tf ∧ C G ψ ∈ tf, 
4.1.1 Let tf be a world such that sf ∼fi tf. 
4.1.2 K i C G ψ ∈ sf, from 1 by definiton (cl (C G ψ)), propositonal logic, and Axioms C, K and RN.
4.1.3 K i C G ψ ∈ tf, from 1 by definiton ∼fi.
4.1.4 C G ψ ∈ tf, from 4.1.3, by Axiom T.
4.1.5 C G ψ ∈ tf, from 4.1.4, by propositonal logic, and Axioms T, C, K and RN.
4.2 Case sf ∼fi tf.
4.2.1 ψ ∈ tf, from 4.1
4.2.2 M, tf ⊨ ψ, from 4.2.1, by ih.
4.3 Case sf ∼fi uf, uf ∼fCG tf, from 4.
4.3.1 C G ψ ∈ uf, from 4.1
4.3.2 M, tf ⊨ ψ, from 4, 4.3.1 & 4.3, by the inductive hypothesis for G ≠ ∅.