import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.GeodesicEquation
import PoincareConjecture.Definitions.M63Polygon












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture

open Proofs.M09

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}




theorem m64_isGeodesicOn_of_pullback_velocity_eq_zero
    (D : LeviCivitaData g) {gamma : ℝ → M} {U : Set ℝ}
    (hU : IsOpen U) (hsmooth : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ gamma U)
    (hequation : ∀ t ∈ U, rampHorizontalCovariantDerivative D gamma
      (fun s => curveVelocity (n := n) gamma s) t = 0) :
    g.IsGeodesicOn gamma U := by
  intro t ht
  let E := EuclideanSpace ℝ (Fin n)
  let p := gamma t
  let c := chartAt E p
  let V := U ∩ gamma ⁻¹' c.source
  have hV : IsOpen V := hsmooth.continuousOn.isOpen_inter_preimage hU c.open_source
  have htV : t ∈ V := ⟨ht, mem_chart_source E p⟩
  let q : ℝ → E := fun s => c (gamma s)
  let w : ℝ → E := deriv q
  have hq : ContDiffOn ℝ ∞ q V :=
    (contMDiffOn_chart.comp (hsmooth.mono inter_subset_left) (fun _ hs => hs.2)).contDiffOn
  have hw : ContDiffOn ℝ ∞ w V := hq.deriv_of_isOpen hV (by simp)
  have hdiff (s : ℝ) (hs : s ∈ V) : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) gamma s :=
    (hsmooth.contMDiffAt (hU.mem_nhds hs.1)).mdifferentiableAt (by simp)
  have hqd (s : ℝ) (hs : s ∈ V) : HasDerivAt q (w s) s :=
    ((hq.contDiffAt (hV.mem_nhds hs)).differentiableAt (by simp)).hasDerivAt
  have hvel (s : ℝ) (hs : s ∈ V) :
      chartVectorField p (w s) (gamma s) = curveVelocity (n := n) gamma s :=
    chartVectorField_coordinate_velocity p gamma s (w s) hs.2 (hdiff s hs) (hqd s hs)
  have hode (s : ℝ) (hs : s ∈ V) : HasDerivAt w
      (-coordinateChristoffel (g.pullbackCoefficients c.symm) (q s) (w s) (w s)) s := by
    have hconn := M63.chartVectorField_coordinateChristoffel D p (q s)
      (c.map_source hs.2) (w s) (w s)
    have hbase : c.symm (q s) = gamma s := c.left_inv hs.2
    rw [hbase] at hconn
    have hzero : chartVectorField p
        (deriv w s + coordinateChristoffel (g.pullbackCoefficients c.symm)
          (q s) (w s) (w s)) (gamma s) = 0 := by
      calc
        _ = chartVectorField p (deriv w s) (gamma s) +
            chartVectorField p (coordinateChristoffel (g.pullbackCoefficients c.symm)
              (q s) (w s) (w s)) (gamma s) := by
          simp only [chartVectorField, VectorField.mpullback, map_add]
        _ = chartVectorField p (deriv w s) (gamma s) +
            D.connection (chartVectorField p (w s)) (gamma s)
              (curveVelocity gamma s) := by rw [hconn, hvel s hs]
        _ = rampHorizontalCovariantDerivative D gamma
            (fun u => chartVectorField p (w u) (gamma u)) s :=
          (M62.pullback_chart_field D p (hdiff s hs) hs.2 hV hs w hw).symm
        _ = rampHorizontalCovariantDerivative D gamma
            (fun u => curveVelocity gamma u) s := M62.pullback_congr D (by
          filter_upwards [hV.mem_nhds hs] with u hu
          exact hvel u hu)
        _ = 0 := hequation s hs.1
    have hinv : (mfderiv (𝓡 n) (𝓡 n) c (gamma s)).IsInvertible :=
      ⟨(mdifferentiable_chart (I := 𝓡 n) p).mfderiv hs.2, rfl⟩
    have hcoord := congrArg (mfderiv (𝓡 n) (𝓡 n) c (gamma s)) hzero
    change (mfderiv (𝓡 n) (𝓡 n) c (gamma s))
      ((mfderiv (𝓡 n) (𝓡 n) c (gamma s)).inverse
        (deriv w s + coordinateChristoffel (g.pullbackCoefficients c.symm)
          (q s) (w s) (w s))) = _ at hcoord
    rw [hinv.self_apply_inverse, map_zero] at hcoord
    exact ((hw.contDiffAt (hV.mem_nhds hs)).differentiableAt (by simp)).hasDerivAt
      |>.congr_deriv (eq_neg_of_add_eq_zero_left hcoord)
  have he : extChartAt (𝓡 n) p = c.toPartialEquiv := by
    ext x <;> simp [c]
  refine ⟨p, q, w, ?_⟩
  filter_upwards [hV.mem_nhds htV] with s hs
  rw [he]
  exact ⟨(c.left_inv hs.2).symm, c.map_source hs.2, hqd s hs, hode s hs⟩





theorem m64MinimizingSide_isGeodesicOn
    {D : LeviCivitaData g} {ell : ℝ} {p q : M}
    (side : M63MinimizingGeodesicSide g D ell p q) :
    g.IsGeodesicOn side.map (Icc (0 : ℝ) ell) :=
  fun _ ht => m64_isGeodesicOn_of_pullback_velocity_eq_zero D
    side.domain_open side.smooth side.equation _ (side.interval_subset ht)

end PoincareConjecture
