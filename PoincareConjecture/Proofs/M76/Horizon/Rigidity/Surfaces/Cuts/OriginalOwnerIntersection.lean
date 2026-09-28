import PoincareConjecture.Proofs.M76.Mathlib.SingleVertexSlabCommonEdge









set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [DecidableEq E]

theorem exists_common_owner_edge
    (K : SimplicialComplex ℝ E) {T U : Finset E}
    (hTf : T ∈ K.faces) (hUf : U ∈ K.faces)
    (hT : T.card = 3) (hU : U.card = 3) (hne : T ≠ U)
    {x y : E}
    (hxT : x ∈ convexHull ℝ (T : Set E))
    (hxU : x ∈ convexHull ℝ (U : Set E))
    (hyT : y ∈ convexHull ℝ (T : Set E))
    (hyU : y ∈ convexHull ℝ (U : Set E)) (hxy : x ≠ y) :
    ∃ a b c d : E, a ≠ b ∧ c ≠ a ∧ c ≠ b ∧ d ≠ a ∧ d ≠ b ∧
      T = ({a, b, c} : Finset E) ∧ U = ({a, b, d} : Finset E) ∧
      x ∈ segment ℝ a b ∧ y ∈ segment ℝ a b := by
  classical
  have hx : x ∈ convexHull ℝ ((T ∩ U : Finset E) : Set E) := by
    rw [Finset.coe_inter, ← K.convexHull_inter_convexHull hTf hUf]
    exact ⟨hxT, hxU⟩
  have hy : y ∈ convexHull ℝ ((T ∩ U : Finset E) : Set E) := by
    rw [Finset.coe_inter, ← K.convexHull_inter_convexHull hTf hUf]
    exact ⟨hyT, hyU⟩
  have hpos : 0 < (T ∩ U).card := by
    by_contra hzero
    have hz : (T ∩ U).card = 0 := by omega
    have hempty : (T ∩ U : Finset E) = ∅ := by simpa using hz
    rw [hempty, Finset.coe_empty, convexHull_empty] at hx
    exact hx.elim
  have htwo_le : 2 ≤ (T ∩ U).card := by
    by_contra hlt
    have hcard : (T ∩ U).card = 1 := by omega
    obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hcard
    have hxz : x = z := by
      have : x ∈ convexHull ℝ ({z} : Set E) := by simpa [hz] using hx
      simpa [convexHull_singleton, mem_singleton_iff] using this
    have hyz : y = z := by
      have : y ∈ convexHull ℝ ({z} : Set E) := by simpa [hz] using hy
      simpa [convexHull_singleton, mem_singleton_iff] using this
    exact hxy (hxz.trans hyz.symm)
  have hinter_ne : T ∩ U ≠ T := by
    intro h
    apply hne
    exact Finset.eq_of_subset_of_card_le
      (h ▸ Finset.inter_subset_right) (by omega)
  have hinter_lt : (T ∩ U).card < T.card := by
    exact Finset.card_lt_card
      (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_left, hinter_ne⟩)
  have hinter : (T ∩ U).card = 2 := by omega
  obtain ⟨a, b, hab, hab'⟩ := Finset.card_eq_two.mp hinter
  have hpT : ({a, b} : Finset E) ⊆ T := by
    rw [← hab']
    exact Finset.inter_subset_left
  have hpU : ({a, b} : Finset E) ⊆ U := by
    rw [← hab']
    exact Finset.inter_subset_right
  obtain ⟨c, hc, hTc⟩ := Finset.exists_eq_insert_iff.mpr
    ⟨hpT, by simp [hT, hab]⟩
  obtain ⟨d, hd, hUd⟩ := Finset.exists_eq_insert_iff.mpr
    ⟨hpU, by simp [hU, hab]⟩
  have hca : c ≠ a := by intro h; exact hc (h ▸ Finset.mem_insert_self _ _)
  have hcb : c ≠ b := by intro h; exact hc (h ▸ Finset.mem_insert_of_mem (by simp))
  have hda : d ≠ a := by intro h; exact hd (h ▸ Finset.mem_insert_self _ _)
  have hdb : d ≠ b := by intro h; exact hd (h ▸ Finset.mem_insert_of_mem (by simp))
  refine ⟨a, b, c, d, hab, hca, hcb, hda, hdb, ?_, ?_, ?_, ?_⟩
  · rw [hTc.symm]
    ext z
    simp [or_comm, or_left_comm, or_assoc]
  · rw [hUd.symm]
    ext z
    simp [or_comm, or_left_comm, or_assoc]
  · rw [← convexHull_pair]
    simpa [hab'] using hx
  · rw [← convexHull_pair]
    simpa [hab'] using hy

end Geometry.SimplicialComplex
