import PoincareConjecture.Proofs.M76.Mathlib.PolygonStrictSigns
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallConnected
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false

open Set

namespace Polygon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ}

theorem exists_two_zero_points_of_both_signs (P : Polygon E (n + 3))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P)
    (A : E → ℝ) (hA : ContinuousOn A (P.boundary ℝ))
    (hneg : ∃ x ∈ P.boundary ℝ, A x < 0)
    (hpos : ∃ x ∈ P.boundary ℝ, 0 < A x) :
    ∃ a b : E, a ≠ b ∧ a ∈ P.boundary ℝ ∧ A a = 0 ∧
      b ∈ P.boundary ℝ ∧ A b = 0 := by
  obtain ⟨u, hu, huA⟩ := hneg
  obtain ⟨v, hv, hvA⟩ := hpos
  have huv : u ≠ v := by
    intro h
    exact lt_asymm (h ▸ huA) hvA
  obtain ⟨U, V, hU, hV, hcover, hinter⟩ := P.exists_arcs_at_marks hP hinj hu hv huv
  have hUs : U ⊆ P.boundary ℝ := subset_union_left.trans hcover.subset
  have hVs : V ⊆ P.boundary ℝ := subset_union_right.trans hcover.subset
  obtain ⟨a, ha, haA⟩ := hU.isConnected.isPreconnected.intermediate_value
    (hU.1 (by simp : u ∈ ({u, v} : Set E)))
    (hU.1 (by simp : v ∈ ({u, v} : Set E))) (hA.mono hUs) ⟨huA.le, hvA.le⟩
  obtain ⟨b, hb, hbA⟩ := hV.isConnected.isPreconnected.intermediate_value
    (hV.1 (by simp : u ∈ ({u, v} : Set E)))
    (hV.1 (by simp : v ∈ ({u, v} : Set E))) (hA.mono hVs) ⟨huA.le, hvA.le⟩
  refine ⟨a, b, ?_, hUs ha, haA, hVs hb, hbA⟩
  intro hab
  have hmark := hinter.subset ⟨ha, hab.symm ▸ hb⟩
  have heq : a = u ∨ a = v := by
    simpa only [mem_insert_iff, mem_singleton_iff] using hmark
  rcases heq with rfl | rfl
  · exact huA.ne haA
  · exact hvA.ne' haA

theorem zero_section_eq_pair_of_preconnected_signs (P : Polygon E (n + 3))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P) (A : E → ℝ)
    (hneg : IsPreconnected (P.boundary ℝ ∩ {x | A x < 0}))
    (hpos : IsPreconnected (P.boundary ℝ ∩ {x | 0 < A x}))
    (hsigns : ∀ x ∈ P.boundary ℝ, A x = 0 →
      x ∈ closure (P.boundary ℝ ∩ {y | A y < 0}) ∧
        x ∈ closure (P.boundary ℝ ∩ {y | 0 < A y}))
    {a b : E} (hab : a ≠ b) (ha : a ∈ P.boundary ℝ) (haA : A a = 0)
    (hb : b ∈ P.boundary ℝ) (hbA : A b = 0) :
    P.boundary ℝ ∩ {x | A x = 0} = {a, b} := by
  obtain ⟨U, V, hU, hV, hcover, hinter⟩ := P.exists_arcs_at_marks hP hinj ha hb hab
  have hUs : U ⊆ P.boundary ℝ := subset_union_left.trans hcover.subset
  have hVs : V ⊆ P.boundary ℝ := subset_union_right.trans hcover.subset
  have hUc := hU.isCompact.isClosed
  have hVc := hV.isCompact.isClosed
  have hmarkzero (x : E) (hx : x ∈ ({a, b} : Set E)) : A x = 0 := by
    have heq : x = a ∨ x = b := by
      simpa only [mem_insert_iff, mem_singleton_iff] using hx
    rcases heq with rfl | rfl
    · exact haA
    · exact hbA
  have hsplit {W : Set E} (hW : IsPreconnected W) (hWs : W ⊆ P.boundary ℝ)
      (hnz : ∀ x ∈ W, A x ≠ 0) : W ⊆ U ∨ W ⊆ V := by
    apply isPreconnected_iff_subset_of_disjoint_closed.mp hW U V hUc hVc
      (hWs.trans hcover.symm.subset)
    apply eq_empty_iff_forall_notMem.mpr
    rintro x ⟨hx, hxU, hxV⟩
    exact hnz x hx (hmarkzero x (hinter.subset ⟨hxU, hxV⟩))
  have hnside := hsplit hneg inter_subset_left (fun x hx => (show A x < 0 from hx.2).ne)
  have hpside := hsplit hpos inter_subset_left (fun x hx => (show 0 < A x from hx.2).ne')
  have hnotU : ¬ P.boundary ℝ ⊆ U := by
    obtain ⟨x, hxV, hxmark⟩ := hV.sdiff_nonempty
    exact fun h => hxmark (hinter.subset ⟨h (hVs hxV), hxV⟩)
  have hnotV : ¬ P.boundary ℝ ⊆ V := by
    obtain ⟨x, hxU, hxmark⟩ := hU.sdiff_nonempty
    exact fun h => hxmark (hinter.subset ⟨hxU, h (hUs hxU)⟩)
  have hwhole {Z : Set E} (hZ : IsClosed Z)
      (hnZ : P.boundary ℝ ∩ {x | A x < 0} ⊆ Z)
      (hpZ : P.boundary ℝ ∩ {x | 0 < A x} ⊆ Z) : P.boundary ℝ ⊆ Z := by
    intro x hx
    rcases lt_trichotomy (A x) 0 with hn | hz | hp
    · exact hnZ ⟨hx, hn⟩
    · exact (closure_minimal hpZ hZ) (hsigns x hx hz).2
    · exact hpZ ⟨hx, hp⟩
  have hzeroSubset : P.boundary ℝ ∩ {x | A x = 0} ⊆ {a, b} := by
    rcases hnside with hnU | hnV
    · rcases hpside with hpU | hpV
      · exact (hnotU (hwhole hUc hnU hpU)).elim
      · intro x hx
        obtain ⟨hxn, hxp⟩ := hsigns x hx.1 hx.2
        exact hinter.subset ⟨closure_minimal hnU hUc hxn, closure_minimal hpV hVc hxp⟩
    · rcases hpside with hpU | hpV
      · intro x hx
        obtain ⟨hxn, hxp⟩ := hsigns x hx.1 hx.2
        exact hinter.subset ⟨closure_minimal hpU hUc hxp, closure_minimal hnV hVc hxn⟩
      · exact (hnotV (hwhole hVc hnV hpV)).elim
  refine Subset.antisymm hzeroSubset ?_
  intro x hx
  exact ⟨hUs (hU.1 hx), hmarkzero x hx⟩

theorem ncard_zero_eq_two_of_preconnected_signs (P : Polygon E (n + 3))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P)
    (A : E → ℝ) (hA : ContinuousOn A (P.boundary ℝ))
    (hneg : IsPreconnected (P.boundary ℝ ∩ {x | A x < 0}))
    (hpos : IsPreconnected (P.boundary ℝ ∩ {x | 0 < A x}))
    (hsigns : ∀ x ∈ P.boundary ℝ, A x = 0 →
      x ∈ closure (P.boundary ℝ ∩ {y | A y < 0}) ∧
        x ∈ closure (P.boundary ℝ ∩ {y | 0 < A y}))
    (hnegn : ∃ x ∈ P.boundary ℝ, A x < 0)
    (hposn : ∃ x ∈ P.boundary ℝ, 0 < A x) :
    (P.boundary ℝ ∩ {x | A x = 0}).ncard = 2 := by
  obtain ⟨a, b, hab, ha, haA, hb, hbA⟩ :=
    P.exists_two_zero_points_of_both_signs hP hinj A hA hnegn hposn
  exact ncard_eq_two.mpr ⟨a, b, hab,
    P.zero_section_eq_pair_of_preconnected_signs hP hinj A hneg hpos hsigns hab ha haA hb hbA⟩

end Polygon
