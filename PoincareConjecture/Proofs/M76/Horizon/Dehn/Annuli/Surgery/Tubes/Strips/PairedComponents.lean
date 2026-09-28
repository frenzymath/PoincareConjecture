import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Tubes.Strips.PairedAxis
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Arcs.Mathlib.DisjointIntervalUniqueness

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli

private theorem two_connected_carriers_eq_or_swap
    {E : Type*} [TopologicalSpace E] {U V A B : Set E}
    (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B)
    (hneA : A.Nonempty) (hneB : B.Nonempty)
    (hU : IsConnected U) (hV : IsPreconnected V) (hcover : U ∪ V = A ∪ B) :
    (U = A ∧ V = B) ∨ (U = B ∧ V = A) := by
  have hcase {A B : Set E} (hA : IsClosed A) (hB : IsClosed B)
      (hAB : Disjoint A B) (hneB : B.Nonempty) (hc : U ∪ V = A ∪ B)
      (hUA : (U ∩ A).Nonempty) : U = A ∧ V = B := by
    have hsub := subset_of_preconnected_closed_union hA hB hAB hU.isPreconnected
      (subset_union_left.trans hc.subset) hUA
    obtain ⟨y, hy⟩ := hneB
    have hyV : y ∈ V := by
      rcases hc.symm.subset (Or.inr hy) with h | h
      · exact (disjoint_left.mp hAB (hsub h) hy).elim
      · exact h
    exact disjoint_closed_components_unique hA hB hAB hU.isPreconnected hV hc
      hUA ⟨y, hyV, hy⟩
  obtain ⟨x, hx⟩ := hU.nonempty
  rcases hcover.subset (Or.inl hx) with hxA | hxB
  · exact Or.inl (hcase hA hB hAB hneB hcover ⟨x, hx, hxA⟩)
  · exact Or.inr (hcase hB hA hAB.symm hneA
      (hcover.trans (union_comm _ _)) ⟨x, hx, hxB⟩)

theorem SourceCircleDecomposition.paired_source_strip_components
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {f : E → X} {S : Set E}
    (old : SourceCircleDecomposition f S) (i : old.Index) (hmate : old.mate i ≠ i)
    {a b : ℝ} (hab : a < b) (phi : Fin 2 → (ℝ × ℝ) → E)
    (hcont : ∀ j, ContinuousOn (fun s ↦ phi j (0, s)) (Icc a b))
    (hcover : (⋃ j, (fun s ↦ phi j (0, s)) '' Icc a b) =
      old.pieces i ∪ old.pieces (old.mate i))
    (hselected : ∀ j z, z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b →
      (phi j z ∈ old.pieces i ∪ old.pieces (old.mate i) ↔ z.1 = 0))
    (closing : SignedAxisPermutation)
    (hclose : ∀ j, phi j (0, a) = phi (closing.index j) (0, b)) :
    closing.swap = false ∧ ∃ label : Equiv.Perm (Fin 2),
      (∀ j, (fun s ↦ phi j (0, s)) '' Icc a b =
        if label j = 0 then old.pieces i else old.pieces (old.mate i)) ∧
      ∀ j z, z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b →
        (phi j z ∈ (if label j = 0 then old.pieces i else old.pieces (old.mate i)) ↔
          z.1 = 0) := by
  classical
  let U := fun j ↦ (fun s ↦ phi j (0, s)) '' Icc a b
  have hdis : Disjoint (old.pieces i) (old.pieces (old.mate i)) :=
    old.disjoint hmate.symm
  have hconn (j : Fin 2) : IsConnected (U j) :=
    (isConnected_Icc hab.le).image _ (hcont j)
  have hc : U 0 ∪ U 1 = old.pieces i ∪ old.pieces (old.mate i) := by
    have hu : U 0 ∪ U 1 = ⋃ j, U j := by
      ext x
      constructor
      · rintro (hx | hx)
        · exact mem_iUnion.mpr ⟨0, hx⟩
        · exact mem_iUnion.mpr ⟨1, hx⟩
      · intro hx
        obtain ⟨j, hj⟩ := mem_iUnion.mp hx
        fin_cases j
        · exact Or.inl hj
        · exact Or.inr hj
    exact hu.trans hcover
  have hcases := two_connected_carriers_eq_or_swap
    (old.pieces_isCompact i).isClosed (old.pieces_isCompact (old.mate i)).isClosed
    hdis (old.pieces_isConnected i).nonempty (old.pieces_isConnected (old.mate i)).nonempty
    (hconn 0) (hconn 1).isPreconnected hc
  have hUdis : Disjoint (U 0) (U 1) := by
    rcases hcases with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · simpa only [h0, h1] using hdis
    · simpa only [h0, h1] using hdis.symm
  have hswap : closing.swap = false := by
    cases hs : closing.swap with
    | false => rfl
    | true =>
      have heq : phi 0 (0, a) = phi 1 (0, b) := by
        simpa [SignedAxisPermutation.index, jointSheetIndex, hs] using hclose 0
      exact (disjoint_left.mp hUdis ⟨a, ⟨le_rfl, hab.le⟩, rfl⟩
        ⟨b, ⟨hab.le, le_rfl⟩, heq.symm⟩).elim
  have hlabel : ∃ label : Equiv.Perm (Fin 2), ∀ j,
      U j = if label j = 0 then old.pieces i else old.pieces (old.mate i) := by
    rcases hcases with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · refine ⟨Equiv.refl _, ?_⟩
      intro j
      fin_cases j
      · simpa using h0
      · simpa using h1
    · refine ⟨Equiv.swap 0 1, ?_⟩
      intro j
      fin_cases j <;> simp_all
  obtain ⟨label, hl⟩ := hlabel
  refine ⟨hswap, label, hl, ?_⟩
  intro j z hz
  constructor
  · intro h
    apply (hselected j z hz).mp
    split_ifs at h with he
    · exact Or.inl h
    · exact Or.inr h
  · intro hz0
    rw [← hl j]
    exact ⟨z.2, hz.2, congrArg (phi j) (Prod.ext hz0.symm rfl)⟩

end PoincareConjecture.M76.Dehn.Annuli
