import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ReturnTraceCharts
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_BoundaryArcIncidence

noncomputable section
set_option autoImplicit false

open Set
open scoped Topology

namespace PoincareConjecture

theorem m64Intrinsic_return_trace_exactly_two_arcs
    {gamma : ℝ → AnnulusCoordinates} {T : ℝ} (hT : 0 < T)
    (hgamma : ContinuousOn gamma (Icc 0 T)) (hend : gamma 0 = gamma T)
    (hginj : InjOn gamma (Ico 0 T))
    {I : Type*} [Finite I] (f : I → ℝ → AnnulusCoordinates)
    (hc : ∀ i, ContinuousOn (f i) (Icc 0 1))
    (hinj : ∀ i, InjOn (f i) (Icc 0 1))
    (hmeet : ∀ i j, i ≠ j → f i '' Icc 0 1 ∩ f j '' Icc 0 1 ⊆ {f i 0, f i 1})
    (hcover : (⋃ i, f i '' Icc 0 1) = gamma '' Icc 0 T)
    {p : AnnulusCoordinates} (hp : ∃ i, p = f i 0 ∨ p = f i 1) :
    ∃ i j : I, i ≠ j ∧ ∀ k, p ∈ f k '' Icc 0 1 ↔ k = i ∨ k = j := by
  classical
  let S := gamma '' Icc 0 T
  have hsub (i : I) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : f i t ∈ S := by
    change f i t ∈ gamma '' Icc 0 T
    rw [← hcover]
    exact mem_iUnion.mpr ⟨i, t, ht, rfl⟩
  have hpS : p ∈ S := by
    obtain ⟨i, hi⟩ := hp
    rcases hi with rfl | rfl
    · exact hsub i 0 (by simp)
    · exact hsub i 1 (by simp)
  let q : S := ⟨p, hpS⟩
  let g (i : I) (t : ℝ) : S := if ht : t ∈ Icc (0 : ℝ) 1 then
    ⟨f i t, hsub i t ht⟩ else q
  have hgval (i : I) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : (g i t).1 = f i t := by
    simp only [g, dif_pos ht]
  have hgc (i : I) : ContinuousOn (g i) (Icc (0 : ℝ) 1) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have h : Continuous (fun t : Icc (0 : ℝ) 1 =>
        (⟨f i t, hsub i t t.2⟩ : S)) :=
      (hc i).domRestrict.subtype_mk _
    convert h using 1
    funext t
    exact Subtype.ext (hgval i t t.2)
  have hgi (i : I) : InjOn (g i) (Icc (0 : ℝ) 1) := by
    intro s hs t ht hst
    apply hinj i hs ht
    simpa only [hgval i s hs, hgval i t ht] using congrArg Subtype.val hst
  have hmem (i : I) (z : S) :
      z ∈ g i '' Icc (0 : ℝ) 1 ↔ z.1 ∈ f i '' Icc (0 : ℝ) 1 := by
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t, ht, (hgval i t ht).symm⟩
    · rintro ⟨t, ht, heq⟩
      exact ⟨t, ht, Subtype.ext ((hgval i t ht).trans heq)⟩
  have hgmeet : ∀ i j, i ≠ j →
      g i '' Icc 0 1 ∩ g j '' Icc 0 1 ⊆ {g i 0, g i 1} := by
    intro i j hij z hz
    rcases hmeet i j hij ⟨(hmem i z).mp hz.1, (hmem j z).mp hz.2⟩ with hz0 | hz1
    · exact Or.inl (Subtype.ext (hz0.trans (hgval i 0 (by simp)).symm))
    · exact Or.inr (Subtype.ext (hz1.trans (hgval i 1 (by simp)).symm))
  have hgcover : (⋃ i, g i '' Icc 0 1) = univ := by
    apply eq_univ_of_forall
    intro z
    have hz : z.1 ∈ ⋃ i, f i '' Icc 0 1 := hcover.symm ▸ z.2
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    exact mem_iUnion.mpr ⟨i, (hmem i z).mpr hi⟩
  have hq : ∃ i, q = g i 0 ∨ q = g i 1 := by
    obtain ⟨i, hi⟩ := hp
    refine ⟨i, ?_⟩
    rcases hi with hi | hi
    · exact Or.inl (Subtype.ext (hi.trans (hgval i 0 (by simp)).symm))
    · exact Or.inr (Subtype.ext (hi.trans (hgval i 1 (by simp)).symm))
  obtain ⟨i, j, hij, hmembers⟩ := m64Intrinsic_exactly_two_boundary_arcs
    (m64Intrinsic_return_trace_real_charts hT hgamma hend hginj)
    g hgc hgi hgmeet hgcover hq
  exact ⟨i, j, hij, fun k => (hmem k q).symm.trans (hmembers k)⟩

end PoincareConjecture
