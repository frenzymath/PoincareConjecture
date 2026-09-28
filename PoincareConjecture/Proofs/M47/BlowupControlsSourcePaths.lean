import PoincareConjecture.Proofs.M47.BlowupControlsSourceScalar
import PoincareConjecture.Proofs.M34.Standard.LocalInverseMetricBound
import PoincareConjecture.Proofs.M34.Standard.CapIntrinsicDiameter

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M47

variable {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F}
  (H : M33RegularHistoryData W) {base : ℝ} (ht : base ∈ H.generalized.interval)

theorem regular_history_inverse_pathELength_le
    {gamma : ℝ → (F.slice base).carrier} {a b : ℝ}
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 gamma (Icc a b))
    (hretain : MapsTo gamma (Icc a b) (range (H.history.forward base ht))) :
    (H.generalized.metric base).pathELength (H.history.inverse base ht ∘ gamma) a b ≤
      (F.metric base).pathELength gamma a b := by
  let e := (regular_history_slice_chart H base ht).toOpenPartialHomeomorph
  have hf : ContMDiffOn (𝓡 3) (𝓡 3) 1 e e.source :=
    (H.history.forward_smooth base ht).of_le (by simp) |>.contMDiffOn
  have hi : ContMDiffOn (𝓡 3) (𝓡 3) 1 e.symm e.target :=
    (H.history.inverse_smooth base ht).of_le (by simp)
  have hbound (y : (F.slice base).carrier) (hy : y ∈ e.target)
      (v : TangentSpace (𝓡 3) y) :
      (H.generalized.metric base).tangentNorm (e.symm y)
        (mfderiv (𝓡 3) (𝓡 3) e.symm y v) ≤ 1 * (F.metric base).tangentNorm y v := by
    apply (H.generalized.metric base).inverse_tangentNorm_le_of_forward_lower_bound
      (F.metric base) e hf hi hy
    intro w
    have heq := congrArg Real.sqrt (H.history.metric_pullback base ht (e.symm y) w w)
    change (F.metric base).tangentNorm (e (e.symm y))
      (mfderiv (𝓡 3) (𝓡 3) e (e.symm y) w) =
        (H.generalized.metric base).tangentNorm (e.symm y) w at heq
    rw [one_mul, heq]
  have hlength := (F.metric base).pathELength_comp_le_of_pointwise_tangentNorm_le
    (H.generalized.metric base) e.symm
    (fun y hy => (hi y hy).contMDiffAt (e.open_target.mem_nhds hy))
    (by norm_num : (0 : ℝ) ≤ 1) hbound gamma a b hgamma hretain
  have hiFun : (e.symm : (F.slice base).carrier → (H.generalized.slice base).carrier) =
      H.history.inverse base ht := rfl
  rw [hiFun] at hlength
  simpa only [ENNReal.ofReal_one, one_mul] using hlength

theorem regular_history_path_prefix_scalar_bound
    {Q A D s : ℝ} (hQ : 0 < Q)
    (x : (H.generalized.slice base).carrier)
    (hscale : H.generalized.scalar ⟨base, x⟩ = Q)
    (hestimate : RepairedBoundedDistanceEstimate H.generalized A D base x)
    {gamma : ℝ → (F.slice base).carrier}
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 gamma (Icc 0 1))
    (hzero : gamma 0 = H.history.forward base ht x)
    (hlength : (F.metric base).pathELength gamma 0 1 < ENNReal.ofReal (A / Real.sqrt Q))
    (hs : s ∈ Icc (0 : ℝ) 1)
    (hretain : MapsTo gamma (Icc 0 s) (range (H.history.forward base ht))) :
    (F.connection base).scalarCurvature (gamma s) ≤ D * Q := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : (F.slice base).carrier → Type _) :=
    ⟨(F.metric base).toRiemannianMetric⟩
  have hsub : Icc (0 : ℝ) s ⊆ Icc 0 1 := Icc_subset_Icc le_rfl hs.2
  have hprefix := hgamma.mono hsub
  have hinverse : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1
      (H.history.inverse base ht ∘ gamma) (Icc 0 s) :=
    ((H.history.inverse_smooth base ht).of_le (by simp)).comp hprefix hretain
  have hdist := (H.generalized.metric base).edist_le_pathELength_of_mem_Icc hinverse
    (show s ∈ Icc (0 : ℝ) s from ⟨hs.1, le_rfl⟩)
  have hlen := regular_history_inverse_pathELength_le H ht hprefix hretain
  have hmono : (F.metric base).pathELength gamma 0 s ≤
      (F.metric base).pathELength gamma 0 1 := Manifold.pathELength_mono le_rfl hs.2
  have hball : H.history.inverse base ht (gamma s) ∈
      (H.generalized.metric base).ball x (A / Real.sqrt Q) := by
    simpa only [RiemannianMetric.ball, mem_ofPred_eq, Function.comp_apply,
      hzero, H.history.left_inverse base ht x] using
      hdist.trans_lt (hlen.trans_lt (hmono.trans_lt hlength))
  have hradius : A / Real.sqrt Q = A * Q ^ (-1 / 2 : ℝ) := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring,
      Real.rpow_neg hQ.le, ← Real.sqrt_eq_rpow, div_eq_mul_inv]
  have hscalar := hestimate (H.history.inverse base ht (gamma s))
    (by simpa only [hscale, hradius] using hball)
  rw [hscale] at hscalar
  have hread := H.scalar_pullback base ht (H.history.inverse base ht (gamma s))
  rw [H.history.right_inverse base ht (hretain ⟨hs.1, le_rfl⟩)] at hread
  exact hread.trans_le hscalar

end PoincareConjecture.M47
