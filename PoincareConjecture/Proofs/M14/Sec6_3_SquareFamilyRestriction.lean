import PoincareConjecture.Proofs.M14.Sec6_3_SquareFamilyAction

set_option autoImplicit false

open Set
open scoped Manifold ContDiff intervalIntegral

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem squareFamilyAction_interval_contDiffOn
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) {a b l r : ℝ} (hab : a < b)
    {U : Set P} (hU : IsOpen U) {γ : ℝ × P → G.Point}
    (hγ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, P))) (spacetimeModel n) ∞ γ (Icc a b ×ˢ U))
    (hl : l ∈ Icc a b) (hr : r ∈ Icc a b) :
    ContDiffOn ℝ ∞ (squareFamilyAction G γ (Icc a b) l r) U := by
  have h := (squareFamilyAction_contDiffOn hM12 hab hU hγ hr).sub
    (squareFamilyAction_contDiffOn hM12 hab hU hγ hl)
  apply h.congr
  intro p hp
  have hd : ContinuousOn (fun s => squareCurveDensity G (fun t => γ (t, p)) (Icc a b) s)
      (Icc a b) :=
    (squareFamilyDensity_contDiffOn hM12 (uniqueDiffOn_Icc hab) hU hγ).continuousOn.comp
      (continuous_id.prodMk continuous_const).continuousOn (fun _ hs => ⟨hs, hp⟩)
  have hIr := (hd.mono (show Icc a r ⊆ Icc a b from
    fun _ hs => ⟨hs.1, hs.2.trans hr.2⟩)).intervalIntegrable_of_Icc
      (μ := MeasureTheory.volume) hr.1
  have hIl := (hd.mono (show Icc a l ⊆ Icc a b from
    fun _ hs => ⟨hs.1, hs.2.trans hl.2⟩)).intervalIntegrable_of_Icc
      (μ := MeasureTheory.volume) hl.1
  exact (intervalIntegral.integral_interval_sub_left hIr hIl).symm

end PoincareConjecture.M14
