import PoincareLib.Geometry.Riemannian.Comparison.Volume.Conjugate.Variation.Intrinsic
import PoincareLib.Geometry.Riemannian.Coordinates.Exponential.SmoothExtension

/-! # Geodesic slices in the second-variation formula

The retained geodesic predicate supplies the zero-acceleration identities of
the central slice and the junction slices. Supports Morgan--Tian,
Theorem 1.34, p. 19.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold Bundle

namespace PoincareMT.ConjugateVariation

open CoordinateExponential ConnectionVariation

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- A coordinate family whose affine slice agrees locally with a geodesic has
zero covariant acceleration in the slice direction. -/
theorem covDerivAlong_fderiv_eq_zero_of_geodesic
    (g : RiemannianMetric n M) (a : M)
    {q : ℝ → M} {S : Set ℝ} {t : ℝ} (hq : g.IsGeodesicOn q S) (ht : t ∈ S)
    (ha : q t ∈ (extChartAt (𝓡 n) a).source)
    {u : P → EuclideanSpace ℝ (Fin n)} {c : ℝ → P} {d : P}
    (hu : ContDiffAt ℝ 2 u (c t)) (hc : ∀ s, HasDerivAt c d s)
    (heq : u ∘ c =ᶠ[𝓝 t] (extChartAt (𝓡 n) a) ∘ q) :
    covDerivAlong (christoffelBilinear
      (g.pullbackCoefficients (extChartAt (𝓡 n) a).symm)) u
      (fun p => fderiv ℝ u p d) d (c t) = 0 := by
  let A := christoffelBilinear (g.pullbackCoefficients (extChartAt (𝓡 n) a).symm)
  let Y := fun p => fderiv ℝ u p d
  have hY1 : ContDiffAt ℝ 1 Y (c t) :=
    (hu.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const
  have hY : DifferentiableAt ℝ Y (c t) := hY1.differentiableAt (by norm_num)
  have hderiv : deriv (u ∘ c) =ᶠ[𝓝 t] Y ∘ c := by
    have hevent : ∀ᶠ s in 𝓝 t, ContDiffAt ℝ 2 u (c s) :=
      (hc t).continuousAt.eventually (hu.eventually (by simp))
    filter_upwards [hevent] with s hs
    exact ((hs.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt s (hc s)).deriv
  have hfield : Y ∘ c =ᶠ[𝓝 t] deriv ((extChartAt (𝓡 n) a) ∘ q) :=
    hderiv.symm.trans heq.deriv
  have hode := hq.hasDerivAt_chart_at ht a ha
  rw [← covDerivAlong_comp_curve A (hu.differentiableAt (by norm_num)) hY (hc t),
    covDerivAlong_congr_base A _ heq, covDerivAlong_congr A _ hfield]
  change deriv (deriv ((extChartAt (𝓡 n) a) ∘ q)) t +
    A (extChartAt (𝓡 n) a (q t)) (deriv ((extChartAt (𝓡 n) a) ∘ q) t)
      (deriv ((extChartAt (𝓡 n) a) ∘ q) t) = 0
  have hacc : deriv (deriv ((extChartAt (𝓡 n) a) ∘ q)) t =
      -A (extChartAt (𝓡 n) a (q t)) (deriv ((extChartAt (𝓡 n) a) ∘ q) t)
        (deriv ((extChartAt (𝓡 n) a) ∘ q) t) := hode.2.deriv
  rw [hacc]
  exact neg_add_cancel _

end PoincareMT.ConjugateVariation
