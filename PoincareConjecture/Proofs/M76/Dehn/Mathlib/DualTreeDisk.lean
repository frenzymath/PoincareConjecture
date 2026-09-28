import PoincareConjecture.Proofs.M76.Dehn.Mathlib.DualLeafAttachment
import Mathlib.Combinatorics.SimpleGraph.Acyclic

set_option autoImplicit false

open Set

namespace SimpleGraph

private noncomputable def induceEraseIso {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) (p : (S : Set V)) :
    (G.induce (S : Set V)).induce ({p}ᶜ : Set (S : Set V)) ≃g
      G.induce (S.erase p.val : Set V) where
  toEquiv :=
    { toFun := fun q => ⟨q.val.val, Finset.mem_erase.mpr
        ⟨fun h => q.property (mem_singleton_iff.mpr (Subtype.ext h)), q.val.property⟩⟩
      invFun := fun q => ⟨⟨q.val, (Finset.mem_erase.mp q.property).2⟩, by
        intro h
        exact (Finset.mem_erase.mp q.property).1
          (congrArg Subtype.val (mem_singleton_iff.mp h))⟩
      left_inv := fun _ => Subtype.ext (Subtype.ext rfl)
      right_inv := fun _ => Subtype.ext rfl }
  map_rel_iff' := by intros; rfl

end SimpleGraph

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  (K : SimplicialComplex ℝ E) [Fintype K.faces]

theorem isFinitePLBallPair_vertexDualUnion_of_induced_tree
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ e ∈ K.faces, e.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2)
    (hlinks : ∀ p ∈ K.vertices, IsConnected (K.link p).space)
    (S : Finset K.vertices)
    (htree : (K.vertexAbstractComplex.edgeGraph.induce (S : Set K.vertices)).IsTree) :
    IsFinitePLBallPair (ℝ × ℝ) (K.vertexDualUnion (S : Set K.vertices))
      (K.vertexDualRim (S : Set K.vertices)) := by
  classical
  revert htree
  refine S.strongInductionOn ?_
  intro A ih hA
  rcases subsingleton_or_nontrivial (A : Set K.vertices) with hsub | hnt
  · let : Subsingleton (A : Set K.vertices) := hsub
    obtain ⟨p⟩ := hA.connected.nonempty
    have hset : (A : Set K.vertices) = {p.val} := by
      ext v
      constructor
      · intro hv
        exact mem_singleton_iff.mpr
          (congrArg Subtype.val (Subsingleton.elim (⟨v, hv⟩ : (A : Set K.vertices)) p))
      · rintro rfl
        exact p.property
    rw [hset, K.vertexDualUnion_singleton, K.vertexDualRim_singleton]
    exact K.isFinitePLBallPair_barycentricDualBlock_vertex hpure hcofaces
      p.val.property (hlinks p.val.val p.val.property)
  · let : Nontrivial (A : Set K.vertices) := hnt
    obtain ⟨p, hp⟩ := hA.exists_vert_degree_one_of_nontrivial
    obtain ⟨q, hpq, hunique⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hp
    have hrem : (K.vertexAbstractComplex.edgeGraph.induce
        (A.erase p.val : Set K.vertices)).IsTree := by
      apply (SimpleGraph.induceEraseIso K.vertexAbstractComplex.edgeGraph A p).isTree_iff.mp
      exact ⟨hA.connected.induce_compl_singleton_of_degree_eq_one hp,
        hA.isAcyclic.induce {p}ᶜ⟩
    have hsmall := ih (A.erase p.val) (Finset.erase_ssubset p.property) hrem
    have hq : q.val ∈ A.erase p.val := Finset.mem_erase.mpr
      ⟨fun h => hpq.ne (Subtype.ext h.symm), q.property⟩
    have hedge : ({p.val.val, q.val.val} : Finset E) ∈ K.faces := by
      have h := hpq.2
      change ({p.val, q.val} : Finset K.vertices).map (Function.Embedding.subtype _) ∈
        K.faces at h
      simpa only [Finset.map_insert, Finset.map_singleton, Function.Embedding.coe_subtype]
        using h
    have hleaf (r : K.vertices) (hr : r ∈ A.erase p.val)
        (hpr : ({p.val.val, r.val} : Finset E) ∈ K.faces) : r = q.val := by
      let rA : (A : Set K.vertices) := ⟨r, (Finset.mem_erase.mp hr).2⟩
      have hadj : (K.vertexAbstractComplex.edgeGraph.induce (A : Set K.vertices)).Adj p rA := by
        refine ⟨?_, ?_⟩
        · intro h
          have he : p.val = r := h
          exact (Finset.mem_erase.mp hr).1 he.symm
        · change ({p.val, r} : Finset K.vertices).map (Function.Embedding.subtype _) ∈ K.faces
          simpa only [Finset.map_insert, Finset.map_singleton, Function.Embedding.coe_subtype]
            using hpr
      exact congrArg Subtype.val (hunique rA hadj)
    have hnew := K.isFinitePLBallPair_vertexDualUnion_insert_of_leaf hpure hcofaces hlinks
      (S := (A.erase p.val : Set K.vertices)) (Finset.notMem_erase p.val A)
      hq hedge hleaf hsmall
    have hset : insert p.val (A.erase p.val : Set K.vertices) = (A : Set K.vertices) := by
      rw [← Finset.coe_insert, Finset.insert_erase p.property]
    rwa [hset] at hnew

end Geometry.SimplicialComplex
