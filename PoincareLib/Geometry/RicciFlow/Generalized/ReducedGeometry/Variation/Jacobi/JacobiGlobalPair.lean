import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.Jacobi.JacobiLocalUniqueness
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.Jacobi.JacobiGaugeCover
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.Jacobi.JacobiGluing
import PoincareLib.Geometry.RicciFlow.Generalized.Gauge.Geometry

/-!
# Global closed-interval horizontal Jacobi transport

Morgan-Tian Lemmas 6.10 and 6.12, pp. 109-110. Local compatible
gauge solutions glue across a finite interval chain. The same local
linear uniqueness identifies every global solution with the prescribed
initial phase value, without extending the base curve off its domain.
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

private noncomputable def horizontalPhaseEncoding (s : ℝ) :
    (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ≃
      G.Horizontal (R.curve s) × G.Horizontal (R.curve s) :=
  let e := (VectorBundle.continuousLinearEquivAt ℝ (EuclideanSpace ℝ (Fin n))
    G.Horizontal (R.curve s)).symm.toEquiv
  e.prodCongr e

/-- Every initial horizontal phase value has a smooth actual Jacobi
pair on the full closed square interval, Lemmas 6.10 and 6.12,
pp. 109-110. -/
theorem exists_horizontalJacobiPair
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (z₀ : G.Horizontal (R.curve (Real.sqrt τ₁)) × G.Horizontal (R.curve (Real.sqrt τ₁))) :
    ∃ z : ∀ s, G.Horizontal (R.curve s) × G.Horizontal (R.curve s),
      IsHorizontalJacobiPairOn R (Real.sqrt τ₁) (Real.sqrt τ₂) z ∧
        z (Real.sqrt τ₁) = z₀ := by
  classical
  have hCoordinates := hM12.coordinate_gauges X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover G.leafwise
  have hscalar := ((hM12.leafwise_calculus X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover).2 G.leafwise).scalar_smooth
  obtain ⟨m, t, b, l, r, β, hm, ht, hta, htb, hp⟩ := exists_overlapping_squareRoot_gauges R
  let W := fun i => Classical.choice (ordinaryGaugeWitness_nonempty (b i) hCoordinates)
  apply exists_dependent_interval_solution_of_overlapping_cover (IsHorizontalJacobiPairOn R)
    (horizontalJacobiPairOn_locality R) (horizontalPhaseEncoding R)
    (Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt) hm t l r ht hta htb ?_ ?_ ?_ z₀
  · intro i
    obtain ⟨hal, hlr, hrb, hlt, htr, hβ, hrec, hclock, hnear⟩ := hp i
    exact ⟨hal, hlr, hrb, hlt, htr, hnear⟩
  · intro i s hs z
    obtain ⟨hal, hlr, hrb, hlt, htr, hβ, hrec, hclock, hnear⟩ := hp i
    exact exists_gaugeHorizontalJacobiPair R (b i) hCoordinates hscalar (W i) hM04 (β i s).2
      hlr (Icc_subset_Icc hal hrb) hβ hrec hclock hs z
  · intro i c d hlc hcd hdr f g hf hg s hs hinit
    obtain ⟨hal, hlr, hrb, hlt, htr, hβ, hrec, hclock, hnear⟩ := hp i
    have hsub : Icc c d ⊆ Icc (l i) (r i) := Icc_subset_Icc hlc hdr
    exact gaugeHorizontalJacobiPair_unique (b i) hCoordinates hscalar (W i) hM04 (β i s).2
      (hβ.mono hsub) (fun v hv => hrec v (hsub hv)) (fun v hv => hclock v (hsub hv))
      hf hg hs hinit

/-- Global actual Jacobi phase solutions with the same initial
value agree on the full closed square interval, Lemmas 6.10 and
6.12, pp. 109-110. -/
theorem horizontalJacobiPair_unique
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    {f g : ∀ s, G.Horizontal (R.curve s) × G.Horizontal (R.curve s)}
    (hf : IsHorizontalJacobiPairOn R (Real.sqrt τ₁) (Real.sqrt τ₂) f)
    (hg : IsHorizontalJacobiPairOn R (Real.sqrt τ₁) (Real.sqrt τ₂) g)
    (hinit : f (Real.sqrt τ₁) = g (Real.sqrt τ₁)) :
    ∀ s ∈ M14SqrtParameterInterval τ₁ τ₂, f s = g s := by
  classical
  have hCoordinates := hM12.coordinate_gauges X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover G.leafwise
  have hscalar := ((hM12.leafwise_calculus X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover).2 G.leafwise).scalar_smooth
  obtain ⟨m, t, b, l, r, β, hm, ht, hta, htb, hp⟩ := exists_overlapping_squareRoot_gauges R
  let W := fun i => Classical.choice (ordinaryGaugeWitness_nonempty (b i) hCoordinates)
  apply dependent_interval_solution_unique_of_cover (IsHorizontalJacobiPairOn R)
    (horizontalJacobiPairOn_locality R) (horizontalPhaseEncoding R)
    hm t l r ht hta htb ?_ ?_ hf hg hinit
  · intro i
    obtain ⟨hal, hlr, hrb, hlt, htr, hβ, hrec, hclock, hnear⟩ := hp i
    exact ⟨hal, hlr, hrb, hlt, htr⟩
  · intro i f' g' hf' hg' s hs heq
    obtain ⟨hal, hlr, hrb, hlt, htr, hβ, hrec, hclock, hnear⟩ := hp i
    exact gaugeHorizontalJacobiPair_unique (b i) hCoordinates hscalar (W i) hM04 (β i s).2
      hβ hrec hclock hf' hg' hs heq

end PoincareMT.M14
