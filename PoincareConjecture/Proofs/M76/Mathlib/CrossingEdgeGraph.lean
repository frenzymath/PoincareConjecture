import PoincareConjecture.Proofs.M76.Mathlib.BichromaticTriangle
import PoincareConjecture.Proofs.M76.Mathlib.FiniteCycleLabels
import Mathlib.AlgebraicTopology.SimplicialComplex.Basic










set_option autoImplicit false

open Set

namespace PreAbstractSimplicialComplex

variable {V : Type*} [DecidableEq V]




def crossingEdgeGraph (A : PreAbstractSimplicialComplex V) (c : V → Bool) :
    SimpleGraph {e : Finset V | e ∈ A.faces ∧ e.IsBichromaticPair c} where
  Adj e f := e ≠ f ∧ ∃ t ∈ A.faces, t.card = 3 ∧ e.val ⊆ t ∧ f.val ⊆ t
  symm := ⟨fun _ _ ⟨hne, t, ht, hcard, he, hf⟩ => ⟨hne.symm, t, ht, hcard, hf, he⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩




theorem crossingEdgeGraph_two_neighbors (A : PreAbstractSimplicialComplex V) (c : V → Bool)
    (hcofaces : ∀ e ∈ A.faces, e.IsBichromaticPair c →
      {t : Finset V | t ∈ A.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2)
    (e : {e : Finset V | e ∈ A.faces ∧ e.IsBichromaticPair c}) :
    ((A.crossingEdgeGraph c).neighborSet e).ncard = 2 := by
  classical
  obtain ⟨t, u, htu, hset⟩ := Set.ncard_eq_two.mp
    (hcofaces e.val e.property.1 e.property.2)
  have ht : t ∈ A.faces ∧ t.card = 3 ∧ e.val ⊆ t := by
    change t ∈ {t : Finset V | t ∈ A.faces ∧ t.card = 3 ∧ e.val ⊆ t}
    rw [hset]
    exact mem_insert _ _
  have hu : u ∈ A.faces ∧ u.card = 3 ∧ e.val ⊆ u := by
    change u ∈ {t : Finset V | t ∈ A.faces ∧ t.card = 3 ∧ e.val ⊆ t}
    rw [hset]
    exact mem_insert_of_mem _ (mem_singleton _)
  obtain ⟨f, hf, hfuniq⟩ := e.property.2.existsUnique_other ht.2.1 ht.2.2
  obtain ⟨g, hg, hgunique⟩ := e.property.2.existsUnique_other hu.2.1 hu.2.2
  have hfA : f ∈ A.faces := (A.isRelLowerSet_faces ht.1).2 hf.2.1
    (Finset.card_pos.mp (by rw [hf.1.card]; decide))
  have hgA : g ∈ A.faces := (A.isRelLowerSet_faces hu.1).2 hg.2.1
    (Finset.card_pos.mp (by rw [hg.1.card]; decide))
  let f' : {e : Finset V | e ∈ A.faces ∧ e.IsBichromaticPair c} := ⟨f, hfA, hf.1⟩
  let g' : {e : Finset V | e ∈ A.faces ∧ e.IsBichromaticPair c} := ⟨g, hgA, hg.1⟩
  have hfg : f' ≠ g' := by
    intro heq
    have hfgval : f = g := congrArg Subtype.val heq
    have htf := Finset.union_eq_triangle e.property.2.card hf.1.card ht.2.1
      ht.2.2 hf.2.1 hf.2.2.symm
    have hug := Finset.union_eq_triangle e.property.2.card hg.1.card hu.2.1
      hu.2.2 hg.2.1 hg.2.2.symm
    exact htu (htf.symm.trans (hfgval ▸ hug))
  have hef : (A.crossingEdgeGraph c).Adj e f' :=
    ⟨fun heq => hf.2.2 (congrArg Subtype.val heq).symm, t, ht.1, ht.2.1, ht.2.2, hf.2.1⟩
  have heg : (A.crossingEdgeGraph c).Adj e g' :=
    ⟨fun heq => hg.2.2 (congrArg Subtype.val heq).symm, u, hu.1, hu.2.1, hu.2.2, hg.2.1⟩
  have hneighbors : (A.crossingEdgeGraph c).neighborSet e = {f', g'} := by
    ext k
    constructor
    · rintro ⟨hne, w, hw, hwcard, hew, hkw⟩
      have hwcoface : w ∈ {t : Finset V | t ∈ A.faces ∧ t.card = 3 ∧ e.val ⊆ t} :=
        ⟨hw, hwcard, hew⟩
      rw [hset] at hwcoface
      have hkne : k.val ≠ e.val := fun h => hne (Subtype.ext h.symm)
      rcases mem_insert_iff.mp hwcoface with rfl | hwcoface
      · exact Or.inl (Subtype.ext (hfuniq k.val ⟨k.property.2, hkw, hkne⟩))
      · have hwU : w = u := mem_singleton_iff.mp hwcoface
        subst w
        exact Or.inr (Subtype.ext (hgunique k.val ⟨k.property.2, hkw, hkne⟩))
    · rintro (rfl | rfl)
      · exact hef
      · exact heg
  rw [hneighbors]
  exact ncard_pair hfg

end PreAbstractSimplicialComplex
