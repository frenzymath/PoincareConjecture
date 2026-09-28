import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Injectivity.Noncollapse
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Generalized.Noncollapse.Volume.LocalVolume
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Bounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace PoincareConjecture.CapCertificate

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M] [SecondCountableTopology M]
  {g : RiemannianMetric 3 M}

theorem core_ball_smaller_volume_lower (N : CapCertificate g)
    {C K R s : ℝ} (hC : N.cap_constant ≤ C) (hK : 0 ≤ K)
    (hcurv : ∀ z ∈ N.carrier, N.connection.curvatureTensorNorm z ≤ K)
    {y : M} (hy : y ∈ N.core) (hrR : N.core_radius y < R)
    (hcompact : IsCompact (closure (g.ball y R))) (hsubset : g.ball y R ⊆ N.carrier)
    (hs : 0 < s) (hsr : s ≤ N.core_radius y) :
    ENNReal.ofReal (RiemannianMetric.modelVolume 3 K s /
      RiemannianMetric.modelVolume 3 K (N.core_radius y)) *
      ENNReal.ofReal (C⁻¹ * N.core_radius y ^ 3) ≤ calibratedMetricVolume g (g.ball y s) := by
  have hr := N.core_radius_pos y hy
  have hCpos := N.cap_constant_pos.trans_le hC
  obtain ⟨b, hb, hvolume⟩ := N.core_ball_volume_lower
  have hCb : C⁻¹ ≤ b :=
    ((inv_le_inv₀ hCpos N.cap_constant_pos).mpr hC).trans hb.le
  have hvol : ENNReal.ofReal (C⁻¹ * N.core_radius y ^ 3) ≤
      g.volumeMeasure (g.ball y (N.core_radius y)) := by
    rw [← Generalized.Noncollapse.calibratedMetricVolume_eq_volumeMeasure]
    exact (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hCb (pow_pos hr 3).le)).trans (hvolume y hy)
  have hRic : ∀ z ∈ g.ball y R, ∀ v : TangentSpace (𝓡 3) z,
      -(((3 : ℝ) - 1) * K) * g.inner z v v ≤ N.connection.ricci z v v :=
    fun z hz v => N.connection.ricci_quadratic_lower_bound_of_curvatureTensorNorm_le
      z (hcurv z (hsubset hz)) v
  have hcompare := g.smallBall_volume_lower_bound_of_precompact_ball y (by norm_num)
    (hr.trans hrR) hK hcompact N.connection hRic hs hsr hrR
  rw [Generalized.Noncollapse.calibratedMetricVolume_eq_volumeMeasure,
    ENNReal.ofReal_div_of_pos (RiemannianMetric.modelVolume_pos (by norm_num) hK hr)]
  exact (mul_le_mul_right hvol _).trans hcompare

end PoincareConjecture.CapCertificate
