import PoincareConjecture.Proofs.M35.CapGeometry.IntrinsicRadialDistance
import PoincareConjecture.Proofs.M35.CapGeometry.FarTipAngularScale

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace PoincareConjecture.M35.Uniqueness

theorem intrinsicWarpingRadius_radialArclength
    (g : RiemannianMetric 3 StandardCapSpace)
    (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        g.inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
    (hcomplete : MetricComplete g) (r : ℝ) :
    intrinsicWarpingRadius g hrotation hcomplete (radialArclength g r) =
      axisWarpingRadius g r := by
  change axisWarpingRadius g ((radialArclengthOrderIso g hrotation hcomplete).symm
    ((radialArclengthOrderIso g hrotation hcomplete) r)) = _
  rw [OrderIso.symm_apply_apply]

end PoincareConjecture.M35.Uniqueness

namespace PoincareConjecture.M35.OrdinaryRealization

open Uniqueness

theorem blowupSequence_intrinsic_center_limits
    (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (hd : Tendsto (fun k => ((E.flow.metric (t k)).edist 0 (x k)).toReal *
      Real.sqrt ((E.flow.connection (t k)).scalarCurvature (x k))) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤)) :
    let Q k := (blowupSequence P E t x ht hR).scale (L.subsequence k)
    let hQ k := (blowupSequence P E t x ht hR).base_scalar_pos (L.subsequence k)
    let G (k : ℕ) : RiemannianMetric 3 StandardCapSpace :=
      M13.scaleSmoothMetric (E.flow.metric (t (L.subsequence k))) (Q k) (hQ k)
    let hrot k := scaleSmoothMetric_rotation_invariant
      (E.rotation_invariant (t (L.subsequence k)) (ht _)) (Q k) (hQ k)
    let hc k := scaleSmoothMetric_complete (E.flow.metric (t (L.subsequence k)))
      (E.complete (t (L.subsequence k)) (ht _)) (Q k) (hQ k)
    let a k := radialArclength (G k) ‖x (L.subsequence k)‖
    Tendsto a atTop atTop ∧ Tendsto (fun k =>
      intrinsicWarpingRadius (G k) (hrot k) (hc k) (a k) ^ 2) atTop (𝓝 2) := by
  dsimp only
  let Q k := (blowupSequence P E t x ht hR).scale (L.subsequence k)
  have hQ (k : ℕ) : 0 < Q k :=
    (blowupSequence P E t x ht hR).base_scalar_pos (L.subsequence k)
  let G (k : ℕ) : RiemannianMetric 3 StandardCapSpace :=
    M13.scaleSmoothMetric (E.flow.metric (t (L.subsequence k))) (Q k) (hQ k)
  have hrot k := scaleSmoothMetric_rotation_invariant
    (E.rotation_invariant (t (L.subsequence k)) (ht _)) (Q k) (hQ k)
  have hc k := scaleSmoothMetric_complete (E.flow.metric (t (L.subsequence k)))
    (E.complete (t (L.subsequence k)) (ht _)) (Q k) (hQ k)
  constructor
  · apply (hd.comp L.subsequence_strictMono.tendsto_atTop).congr'
    filter_upwards [] with k
    have hh := M13.homothety_edist (E.flow.metric (t (L.subsequence k))) (G k)
      (Diffeomorph.refl (𝓡 3) StandardCapSpace ∞) (Q k) (hQ k)
      (M13.identity_metricHomothety _ (Q k) (hQ k)) 0 (x (L.subsequence k))
    have hn : 0 ≤ radialArclength (G k) ‖x (L.subsequence k)‖ := by
      simpa only [radialArclength_zero] using
        (radialArclength_strictMono (G k)).monotone (norm_nonneg (x (L.subsequence k)))
    change (G k).edist 0 (x (L.subsequence k)) = _ at hh
    have h := congrArg ENNReal.toReal hh
    rw [edist_zero_eq_radialArclength (G k) (hrot k) (hc k) P,
      ENNReal.toReal_ofReal hn, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] at h
    rw [show Q k = (E.flow.connection (t (L.subsequence k))).scalarCurvature
      (x (L.subsequence k)) from blowupSequence_scale P E t x ht hR (L.subsequence k)] at h
    exact (mul_comm _ _).trans h.symm
  · have h := blowupSequence_far_tip_normalized_orbit_sq_tendsto_two P E t x ht hR hd L
    apply h.congr'
    filter_upwards [] with k
    rw [intrinsicWarpingRadius_radialArclength, axisWarpingRadius_scale, mul_pow,
      Real.sq_sqrt (hQ k).le]
    rw [show Q k = (E.flow.connection (t (L.subsequence k))).scalarCurvature
      (x (L.subsequence k)) from blowupSequence_scale P E t x ht hR (L.subsequence k)]

end PoincareConjecture.M35.OrdinaryRealization
