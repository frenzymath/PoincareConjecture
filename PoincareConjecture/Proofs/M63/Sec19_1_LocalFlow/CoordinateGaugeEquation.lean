import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C1ChartPullback
import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.GeodesicConnection
import PoincareConjecture.Proofs.M62.Lemma0_1_Speed

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M63

open Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

theorem pullback_velocity_eq_chart_acceleration {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (p : M) {gamma : ℝ → M} {U : Set ℝ}
    (hU : IsOpen U) (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 2 gamma U)
    (hmap : MapsTo gamma U (chartAt E p).source) {x : ℝ} (hx : x ∈ U) :
    let z : ℝ → E := fun r => chartAt E p (gamma r)
    rampHorizontalCovariantDerivative D gamma (fun r => curveVelocity gamma r) x =
      chartVectorField p
        (deriv (deriv z) x + coordinateChristoffel
          (g.pullbackCoefficients (chartAt E p).symm) (z x) (deriv z x) (deriv z x))
        (gamma x) := by
  let z : ℝ → E := fun r => chartAt E p (gamma r)
  change _ = chartVectorField p
    (deriv (deriv z) x + coordinateChristoffel
      (g.pullbackCoefficients (chartAt E p).symm) (z x) (deriv z x) (deriv z x)) (gamma x)
  have hz : ContDiffOn ℝ 2 z U := (contMDiffOn_chart.comp hgamma hmap).contDiffOn
  have hv : ContDiffOn ℝ 1 (deriv z) U := hz.deriv_of_isOpen hU (by norm_num)
  have hdiff (r : ℝ) (hr : r ∈ U) : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) gamma r :=
    ((hgamma r hr).contMDiffAt (hU.mem_nhds hr)).mdifferentiableAt (by norm_num)
  have hvel (r : ℝ) (hr : r ∈ U) :
      chartVectorField p (deriv z r) (gamma r) = curveVelocity gamma r :=
    chartVectorField_coordinate_velocity p gamma r (deriv z r) (hmap hr) (hdiff r hr)
      (((hz r hr).contDiffAt (hU.mem_nhds hr)).differentiableAt (by norm_num)).hasDerivAt
  have hconn := chartVectorField_coordinateChristoffel D p (z x)
    ((chartAt E p).map_source (hmap hx)) (deriv z x) (deriv z x)
  have hbase : (chartAt E p).symm (z x) = gamma x := (chartAt E p).left_inv (hmap hx)
  rw [hbase] at hconn
  calc
    _ = rampHorizontalCovariantDerivative D gamma
        (fun r => chartVectorField p (deriv z r) (gamma r)) x := M62.pullback_congr D (by
      filter_upwards [hU.mem_nhds hx] with r hr
      exact (hvel r hr).symm)
    _ = chartVectorField p (deriv (deriv z) x) (gamma x) +
        D.connection (chartVectorField p (deriv z x)) (gamma x) (curveVelocity gamma x) :=
      pullback_chart_field_of_contDiff_one D p (hdiff x hx) (hmap hx) hU hx (deriv z) hv
    _ = _ := by
      rw [← hvel x hx, ← hconn]
      simp only [chartVectorField, VectorField.mpullback, map_add]

variable {a b : ℝ}

theorem speed_sq_eq_chart_coefficients (F : RicciFlow n M (Icc a b))
    (q : ℝ → ℝ → M) (p : M) {t : ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hspace : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 2 (fun y => q y t) U)
    (hmap : MapsTo (fun y => q y t) U (chartAt E p).source) {x : ℝ} (hx : x ∈ U) :
    let z : ℝ → E := fun y => chartAt E p (q y t)
    curveSpeed F q t x ^ 2 =
      (F.metric t).pullbackCoefficients (chartAt E p).symm (z x) (deriv z x) (deriv z x) := by
  let z : ℝ → E := fun y => chartAt E p (q y t)
  have hz : ContDiffOn ℝ 2 z U := (contMDiffOn_chart.comp hspace hmap).contDiffOn
  have hdiff : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) (fun y => q y t) x :=
    ((hspace x hx).contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by norm_num)
  have hvel := chartVectorField_coordinate_velocity p (fun y => q y t) x (deriv z x)
    (hmap hx) hdiff
    (((hz x hx).contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)).hasDerivAt
  have hbase : (chartAt E p).symm (z x) = q x t := (chartAt E p).left_inv (hmap hx)
  have hcoord : mfderiv (𝓡 n) (𝓡 n) (chartAt E p).symm (z x) (deriv z x) =
      curveVelocity (fun y => q y t) x := by
    rw [← chartVectorField_at_inverse p (deriv z x) (z x)
      ((chartAt E p).map_source (hmap hx)), hbase]
    exact hvel
  rw [M62.speed_sq]
  change (F.metric t).inner (q x t) (curveVelocity (fun y => q y t) x)
      (curveVelocity (fun y => q y t) x) =
    (F.metric t).inner ((chartAt E p).symm (z x))
      (mfderiv (𝓡 n) (𝓡 n) (chartAt E p).symm (z x) (deriv z x))
      (mfderiv (𝓡 n) (𝓡 n) (chartAt E p).symm (z x) (deriv z x))
  erw [hcoord, hbase]

theorem parabolic_gauge_iff_coordinate_equation (F : RicciFlow n M (Icc a b))
    (q : ℝ → ℝ → M) (p : M) {t x : ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hspace : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 2 (fun y => q y t) U)
    (hmap : MapsTo (fun y => q y t) U (chartAt E p).source) (hx : x ∈ U)
    (htime : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) (fun r => q x r) t) :
    let z : ℝ → E := fun y => chartAt E p (q y t)
    (curveVelocity (fun r => q x r) t =
      (curveSpeed F q t x ^ 2)⁻¹ •
        rampHorizontalCovariantDerivative (F.connection t) (fun y => q y t)
          (fun y => curveVelocity (fun r => q r t) y) x) ↔
      deriv (fun r => chartAt E p (q x r)) t =
        (curveSpeed F q t x ^ 2)⁻¹ •
          (deriv (deriv z) x + coordinateChristoffel
            ((F.metric t).pullbackCoefficients (chartAt E p).symm)
            (z x) (deriv z x) (deriv z x)) := by
  let z : ℝ → E := fun y => chartAt E p (q y t)
  let L := mfderiv (𝓡 n) (𝓡 n) (chartAt E p) (q x t)
  have hL : L.IsInvertible :=
    ⟨(mdifferentiable_chart (I := 𝓡 n) p).mfderiv (hmap hx), rfl⟩
  have hinj : Function.Injective L.inverse := by
    intro v w hvw
    simpa only [hL.self_apply_inverse] using congrArg L hvw
  have hvel := chartVectorField_coordinate_velocity p (fun r => q x r) t
    (deriv (fun r => chartAt E p (q x r)) t) (hmap hx) htime
    (hasDerivAt_chart_curve p (fun r => q x r) t (hmap hx) htime).differentiableAt.hasDerivAt
  dsimp only
  rw [← hvel, pullback_velocity_eq_chart_acceleration (F.connection t) p hU hspace hmap hx]
  change L.inverse (deriv (fun r => chartAt E p (q x r)) t) =
      (curveSpeed F q t x ^ 2)⁻¹ • L.inverse
        (deriv (deriv z) x + coordinateChristoffel
          ((F.metric t).pullbackCoefficients (chartAt E p).symm)
          (z x) (deriv z x) (deriv z x)) ↔ _
  rw [← map_smul]
  exact hinj.eq_iff

end PoincareConjecture.M63
