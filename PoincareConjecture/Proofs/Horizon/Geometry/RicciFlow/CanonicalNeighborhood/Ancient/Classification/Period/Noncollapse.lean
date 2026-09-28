import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.IntrinsicCalculus
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Scalar.SharpBounds

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.AncientKappaSolution

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

theorem not_linear_volume_growth_of_scalar_decay
    (K : AncientKappaSolution 3 M)
    (hscalar : ∀ t < 0, ∀ x, (K.flow.connection t).scalarCurvature x ≤ (-t)⁻¹)
    (a C : ℝ) (ha : 0 ≤ a) (hC : 0 ≤ C)
    (hvolume : ∀ t ≤ 0, calibratedMetricVolume (K.flow.metric t) univ ≤
      ENNReal.ofReal (C * (1 - a * t))) : False := by
  let r : ℝ := max 1 (C * (1 + a) / K.kappa + 1)
  have hr1 : 1 ≤ r := le_max_left _ _
  have hr : 0 < r := zero_lt_one.trans_le hr1
  have hsq : 0 < r ^ 2 := sq_pos_of_pos hr
  have hrlarge : C * (1 + a) < K.kappa * r := by
    have h : C * (1 + a) / K.kappa < r := by
      exact (lt_add_one _).trans_le (le_max_right _ _)
    simpa only [mul_comm K.kappa r] using (div_lt_iff₀ K.kappa_pos).mp h
  let p : M := Classical.choice inferInstance
  have hbound : ∀ s ∈ Ioc (-r ^ 2 - r ^ 2) (-r ^ 2),
      ∀ q ∈ (K.flow.metric (-r ^ 2)).ball p r,
        |(K.flow.connection s).curvatureTensorNorm q| ≤ r⁻¹ ^ 2 := by
    intro s hs q _
    have hs0 : s < 0 := hs.2.trans_lt (neg_neg_of_pos hsq)
    rw [abs_of_nonneg
      (show 0 ≤ (K.flow.connection s).curvatureTensorNorm q from Real.sqrt_nonneg _)]
    apply ((K.flow.connection s).curvatureTensorNorm_le_scalarCurvature_sharp
      (K.flow.connection s).intrinsicCurvatureTensorCalculus q
      (K.nonnegative_curvature_operator s hs0.le q)).trans
    apply (hscalar s hs0 q).trans
    rw [inv_pow]
    exact (inv_le_inv₀ (neg_pos.mpr hs0) hsq).mpr (by linarith [hs.2])
  have hn := K.noncollapsed r hr (-r ^ 2) (neg_nonpos.mpr hsq.le) p r hr le_rfl hbound
  have hv := hvolume (-r ^ 2) (neg_nonpos.mpr hsq.le)
  have hle : ENNReal.ofReal (K.kappa * r ^ 3) ≤
      ENNReal.ofReal (C * (1 + a * r ^ 2)) := by
    have hm := hn.trans ((measure_mono (subset_univ _)).trans hv)
    simpa only [mul_neg, sub_neg_eq_add] using hm
  have hle' : K.kappa * r ^ 3 ≤ C * (1 + a * r ^ 2) :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hle
  have hr2 : 1 ≤ r ^ 2 := by nlinarith
  have hvol : C * (1 + a * r ^ 2) ≤ C * (1 + a) * r ^ 2 := by
    nlinarith [mul_nonneg hC (sub_nonneg.mpr hr2)]
  have hcancel : K.kappa * r ≤ C * (1 + a) := by
    apply (mul_le_mul_iff_right₀ hsq).mp
    nlinarith [hle'.trans hvol]
  exact (not_le_of_gt hrlarge) hcancel

end PoincareConjecture.AncientKappaSolution
