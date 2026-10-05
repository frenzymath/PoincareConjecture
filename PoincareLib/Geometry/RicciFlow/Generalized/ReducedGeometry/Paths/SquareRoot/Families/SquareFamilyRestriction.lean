import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Paths.SquareRoot.Families.SquareFamilyAction

/-!
# Smooth actions on arbitrary retained subintervals

Morgan-Tian equation (6.2) and Proposition 6.30, pp. 106, 118-119.
The actual prefix primitives give smooth actions between any two
fixed points of the retained closed time interval. This includes
the continuation action in the broken-cost argument.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff intervalIntegral

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- Every fixed subinterval action of an actual smooth closed-time
family is smooth in its open parameters. Both endpoint orders and
equal endpoints are allowed, equation (6.2), p. 106. -/
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

end PoincareMT.M14
