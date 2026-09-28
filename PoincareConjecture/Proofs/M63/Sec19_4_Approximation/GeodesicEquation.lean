import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.GeodesicConnection
import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.GeodesicSmoothness
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.Uniqueness
import PoincareConjecture.Proofs.M62.Sec19_1_PullbackTorsion










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

open Set Filter
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture.RiemannianMetric

open Proofs.M09

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {gamma : ℝ → M} {S : Set ℝ}

local notation "E" => EuclideanSpace ℝ (Fin n)



theorem IsGeodesicOn.pullback_velocity_eq_zero (hgamma : g.IsGeodesicOn gamma S)
    (D : LeviCivitaData g) {t : ℝ} (ht : t ∈ S) :
    rampHorizontalCovariantDerivative D gamma (fun s => curveVelocity gamma s) t = 0 := by
  let p := gamma t
  obtain ⟨U, hU, htU, hgammaU, _, hmap, _⟩ :=
    hgamma.exists_common_chart_nhds hgamma ht p
      (mem_extChartAt_source p) (mem_extChartAt_source p)
  have he : extChartAt (𝓡 n) p = (chartAt E p).toPartialEquiv := by
    ext x <;> simp
  have hp : MapsTo gamma U (chartAt E p).source := by simpa [he] using hmap
  let q : ℝ → E := fun s => chartAt E p (gamma s)
  let v := deriv q
  have hODE : ∀ s ∈ U, HasDerivAt q (v s) s ∧ HasDerivAt v
      (-coordinateChristoffel (g.pullbackCoefficients (chartAt E p).symm)
        (q s) (v s) (v s)) s := by
    simpa [q, v, he] using hgammaU.hasDerivAt_in_chart hU p hmap
  have hq : ContDiffOn ℝ ∞ q U :=
    (contMDiffOn_chart.comp hgammaU.contMDiffOn_infty hp).contDiffOn
  have hv : ContDiffOn ℝ ∞ v U := hq.deriv_of_isOpen hU (by simp)
  have hdiff (s : ℝ) (hs : s ∈ U) : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) gamma s :=
    (hgammaU.contMDiffAt_infty hs).mdifferentiableAt (by simp)
  have hvel (s : ℝ) (hs : s ∈ U) :
      chartVectorField p (v s) (gamma s) = curveVelocity gamma s :=
    chartVectorField_coordinate_velocity p gamma s (v s) (hp hs) (hdiff s hs)
      (hODE s hs).1
  have hconn := M63.chartVectorField_coordinateChristoffel D p (q t)
    ((chartAt E p).map_source (hp htU)) (v t) (v t)
  have hbase : (chartAt E p).symm (q t) = gamma t := (chartAt E p).left_inv (hp htU)
  rw [hbase] at hconn
  calc
    _ = rampHorizontalCovariantDerivative D gamma
        (fun s => chartVectorField p (v s) (gamma s)) t := M62.pullback_congr D (by
      filter_upwards [hU.mem_nhds htU] with s hs
      exact (hvel s hs).symm)
    _ = chartVectorField p (deriv v t) (gamma t) +
        D.connection (chartVectorField p (v t)) (gamma t) (curveVelocity gamma t) :=
      M62.pullback_chart_field D p (hdiff t htU) (hp htU) hU htU v hv
    _ = 0 := by
      rw [(hODE t htU).2.deriv, ← hvel t htU, ← hconn]
      simp only [chartVectorField, VectorField.mpullback, map_neg, neg_add_cancel]

end PoincareConjecture.RiemannianMetric
