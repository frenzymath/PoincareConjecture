import PoincareConjecture.Proofs.M34.Standard.GeneralizedCylinderVolume
import PoincareConjecture.Proofs.M47.LimitNoncollapseSqueeze

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.M47

theorem limitNoncollapse_source_ball_volume_transfer
    {F : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {origin scale : ℝ} {I : Set ℝ} {U : Set C.carrier}
    (e : GeneralizedFlowCylinder F C origin scale I U)
    (hU : IsOpen U) (h0 : 0 ∈ I) (hscale : 0 < scale)
    (g : RiemannianMetric 3 C.carrier) (o : C.carrier)
    {p : F.point} (hp : e.pointMap 0 h0 o = p) {a : ℝ}
    {V : Set C.carrier} (hV : IsOpen V) (hVU : V ⊆ U)
    (hAV : g.ball o (2 * a) ⊆ V)
    (hlocal : ∀ x ∈ (F.metric p.1).ball p.2 (a / Real.sqrt scale),
      ∃ y ∈ g.ball o (2 * a) ∩ U,
        e.pointMap 0 h0 y = (⟨p.1, x⟩ : F.point))
    (hbound : ∀ x ∈ V, ∀ v : TangentSpace (𝓡 3) x,
      e.pullbackInner 0 h0 x v v ≤ 2 * g.inner x v v) :
    calibratedMetricVolume (F.metric p.1)
        ((F.metric p.1).ball p.2 (a / Real.sqrt scale)) ≤
      ENNReal.ofReal (2 / Real.sqrt scale) ^ 3 *
        calibratedMetricVolume g (g.ball o (2 * a)) := by
  exact e.source_ball_volume_le_of_localization hU h0 hscale g o hp hV hVU hAV
    hlocal hbound

theorem limitNoncollapse_theta_ninth_product {theta kappa r : ℝ}
    (htheta : 0 ≤ theta) :
    ENNReal.ofReal (theta ^ 3) *
        ENNReal.ofReal (kappa * (theta ^ 2 * r) ^ 3) =
      ENNReal.ofReal (kappa * theta ^ 9 * r ^ 3) := by
  rw [← ENNReal.ofReal_mul (pow_nonneg htheta 3)]
  congr 1
  ring

theorem limitNoncollapse_exact_density_of_theta_bounds
    {kappa r : ℝ} {V : ℝ≥0∞}
    (hvolume : ∀ theta ∈ Ioo (0 : ℝ) 1,
      ENNReal.ofReal (kappa * theta ^ 9 * r ^ 3) ≤ V) :
    ENNReal.ofReal (kappa * r ^ 3) ≤ V :=
  limitNoncollapse_theta_ninth_squeeze hvolume

end PoincareConjecture.M47
