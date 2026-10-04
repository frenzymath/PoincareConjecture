import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.AdaptedFields.AdaptedLocalExistence
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.AdaptedFields.AdaptedMetric
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.AdaptedFields.AdaptedGluing
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.Jacobi.JacobiGaugeCover

/-!
# Global actual adapted transport

Closed local gauge solutions glue across the finite overlapping cover
of the actual square-root path. Geometric metric conservation supplies
uniqueness on each overlap. Morgan-Tian Definition 6.35, p. 122, and
the adapted frame of Proposition 6.43, pp. 127-128.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}
  (R : M14SquareRootPath G p)

private noncomputable def horizontalAdaptedEncoding (s : ℝ) :
    EuclideanSpace ℝ (Fin n) ≃ G.Horizontal (R.curve s) :=
  (VectorBundle.continuousLinearEquivAt ℝ (EuclideanSpace ℝ (Fin n))
    G.Horizontal (R.curve s)).symm.toEquiv

/-- Every initial horizontal value has a smooth actual unit-adapted
field on the full closed square interval, Definition 6.35 and
Proposition 6.43, pp. 122, 127-128. -/
theorem exists_horizontalUnitAdaptedField
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (P₀ : G.Horizontal (R.curve (Real.sqrt τ₁))) :
    ∃ P : ∀ s, G.Horizontal (R.curve s),
      IsHorizontalUnitAdaptedFieldOn R (Real.sqrt τ₁) (Real.sqrt τ₂) P ∧
        P (Real.sqrt τ₁) = P₀ := by
  classical
  have hCoordinates := hM12.coordinate_gauges X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover G.leafwise
  obtain ⟨m, t, b, l, r, β, hm, ht, hta, htb, hp⟩ := exists_overlapping_squareRoot_gauges R
  let W := fun i => Classical.choice (ordinaryGaugeWitness_nonempty (b i) hCoordinates)
  apply exists_dependent_interval_solution_of_overlapping_cover (IsHorizontalUnitAdaptedFieldOn R)
    (horizontalUnitAdaptedOn_locality R) (horizontalAdaptedEncoding R)
    (Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt) hm t l r ht hta htb ?_ ?_ ?_ P₀
  · intro i
    obtain ⟨hal, hlr, hrb, hlt, htr, hβ, hrec, hclock, hnear⟩ := hp i
    exact ⟨hal, hlr, hrb, hlt, htr, hnear⟩
  · intro i s hs P₀
    obtain ⟨hal, hlr, hrb, hlt, htr, hβ, hrec, hclock, hnear⟩ := hp i
    exact exists_gaugeHorizontalUnitAdaptedField R (b i) hCoordinates (W i) hM04 (β i s).2
      hlr (Icc_subset_Icc hal hrb) hβ hrec hclock hs P₀
  · intro i c d hlc hcd hdr P Q hP hQ s hs hinit
    exact horizontalUnitAdapted_unique hM12 hP hQ hs hinit

end PoincareMT.M14
