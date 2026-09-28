import PoincareConjecture.Proofs.M35.Sec12_4_Uniqueness.GaugePullbackMetric
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M35.Uniqueness

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

theorem trajectory_eq_of_closed_trace
    {T C : ℝ} (hT : 0 ≤ T) {f g df dg : ℝ → V}
    (hf : ContinuousOn f (Icc 0 T)) (hg : ContinuousOn g (Icc 0 T))
    (hdf : ∀ t ∈ Ioo 0 T, HasDerivAt f (df t) t)
    (hdg : ∀ t ∈ Ioo 0 T, HasDerivAt g (dg t) t)
    (hbound : ∀ t ∈ Ioo 0 T, ‖df t - dg t‖ ≤ C * ‖f t - g t‖)
    (hzero : f 0 = g 0) : EqOn f g (Icc 0 T) := by
  let z := fun t => f t - g t
  let dz := fun t => df t - dg t
  let e := fun t => Real.exp (-2 * C * t) * inner ℝ (z t) (z t)
  let de := fun t => Real.exp (-2 * C * t) *
    (2 * inner ℝ (dz t) (z t) - 2 * C * ‖z t‖ ^ 2)
  have hz : ContinuousOn z (Icc 0 T) := hf.sub hg
  have he : ContinuousOn e (Icc 0 T) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul
      (hz.inner hz)
  have hde (t : ℝ) (ht : t ∈ Ioo 0 T) : HasDerivAt e (de t) t := by
    have hd : HasDerivAt z (dz t) t := (hdf t ht).sub (hdg t ht)
    have hdexp := ((hasDerivAt_id t).const_mul (-2 * C)).exp
    apply (hdexp.mul (HasDerivAt.inner ℝ hd hd)).congr_deriv
    dsimp only [de, id_eq]
    rw [real_inner_self_eq_norm_sq, real_inner_comm (z t) (dz t)]
    ring
  have hnonpos (t : ℝ) (ht : t ∈ Ioo 0 T) : de t ≤ 0 := by
    have hi : inner ℝ (dz t) (z t) ≤ C * ‖z t‖ ^ 2 := by
      calc
        _ ≤ ‖dz t‖ * ‖z t‖ := real_inner_le_norm _ _
        _ ≤ (C * ‖z t‖) * ‖z t‖ :=
          mul_le_mul_of_nonneg_right (hbound t ht) (norm_nonneg _)
        _ = _ := by ring
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (by linarith only [hi])
  have hanti : AntitoneOn e (Icc 0 T) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 T) he
      (fun t ht => (hde t (by simpa only [interior_Icc] using ht)).hasDerivWithinAt)
      (fun t ht => hnonpos t (by simpa only [interior_Icc] using ht))
  intro t ht
  have hle := hanti ⟨le_rfl, hT⟩ ht ht.1
  have he0 : e 0 = 0 := by simp [e, z, hzero]
  rw [he0] at hle
  have hi : inner ℝ (z t) (z t) ≤ 0 := by
    by_contra h
    exact (not_lt_of_ge hle) (mul_pos (Real.exp_pos _) (lt_of_not_ge h))
  have hn : ‖z t‖ ^ 2 = 0 :=
    le_antisymm (by simpa only [real_inner_self_eq_norm_sq] using hi) (sq_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hn))

theorem trajectories_eq_of_local_spatial_bound
    {T : ℝ} (hT : 0 ≤ T) {W : ℝ → V → V} {f g : ℝ → V}
    (hf : ContinuousOn f (Icc 0 T)) (hg : ContinuousOn g (Icc 0 T))
    (hdf : ∀ t ∈ Ioo 0 T, HasDerivAt f (-W t (f t)) t)
    (hdg : ∀ t ∈ Ioo 0 T, HasDerivAt g (-W t (g t)) t)
    (hW : ∀ t ∈ Ioo 0 T, Differentiable ℝ (W t))
    (hbound : ∀ R > 0, ∃ C : ℝ, ∀ t ∈ Ioo 0 T,
      ∀ x ∈ Metric.closedBall (0 : V) R, ‖fderiv ℝ (W t) x‖ ≤ C)
    (hzero : f 0 = g 0) : EqOn f g (Icc 0 T) := by
  obtain ⟨Mf, hMf⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  obtain ⟨Mg, hMg⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  let R := |Mf| + |Mg| + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hfr (t : ℝ) (ht : t ∈ Icc 0 T) : f t ∈ Metric.closedBall (0 : V) R := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (hMf t ht).trans (by dsimp [R]; linarith [le_abs_self Mf, abs_nonneg Mg])
  have hgr (t : ℝ) (ht : t ∈ Icc 0 T) : g t ∈ Metric.closedBall (0 : V) R := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (hMg t ht).trans (by dsimp [R]; linarith [le_abs_self Mg, abs_nonneg Mf])
  obtain ⟨C, hC⟩ := hbound R hR
  apply trajectory_eq_of_closed_trace (C := C) hT hf hg hdf hdg _ hzero
  intro t ht
  have h := (convex_closedBall (0 : V) R).norm_image_sub_le_of_norm_fderiv_le
    (fun x _ => hW t ht x) (hC t ht)
    (hgr t ⟨ht.1.le, ht.2.le⟩) (hfr t ⟨ht.1.le, ht.2.le⟩)
  simpa only [neg_sub_neg, norm_sub_rev] using h

theorem gaugePullbackMetric_symm_recover (g : RiemannianMetric n V)
    (Φ : Diffeomorph (𝓡 n) (𝓡 n) V V ∞) (x u v : V) :
    (gaugePullbackMetric g Φ.symm).inner (Φ x)
      (fderiv ℝ (Φ : V → V) x u) (fderiv ℝ (Φ : V → V) x v) = g.inner x u v := by
  have hΦ : ContDiff ℝ ∞ (Φ : V → V) := contMDiff_iff_contDiff.mp Φ.contMDiff
  have hΨ : ContDiff ℝ ∞ (Φ.symm : V → V) := contMDiff_iff_contDiff.mp Φ.symm.contMDiff
  have hd := ((hΨ.differentiable (by simp) (Φ x)).hasFDerivAt).comp x
    (hΦ.differentiable (by simp) x).hasFDerivAt
  have hcomp : (fun y => Φ.symm (Φ y)) = (id : V → V) :=
    funext Φ.symm_apply_apply
  have hder : (fderiv ℝ (Φ.symm : V → V) (Φ x)).comp (fderiv ℝ (Φ : V → V) x) =
      ContinuousLinearMap.id ℝ V := by
    have h := hd.fderiv
    change fderiv ℝ (fun y => Φ.symm (Φ y)) x = _ at h
    rw [hcomp, fderiv_id] at h
    exact h.symm
  have hdu (a : V) : fderiv ℝ (Φ.symm : V → V) (Φ x)
      (fderiv ℝ (Φ : V → V) x a) = a := by
    change ((fderiv ℝ (Φ.symm : V → V) (Φ x)).comp
      (fderiv ℝ (Φ : V → V) x)) a = a
    rw [hder]
    rfl
  rw [gaugePullbackMetric_inner, hdu u, hdu v, Φ.symm_apply_apply]

theorem metric_eq_of_equal_gauges_and_pushforwards
    (g h : RiemannianMetric n V)
    (Φ Ψ : Diffeomorph (𝓡 n) (𝓡 n) V V ∞)
    (hmap : (Φ : V → V) = Ψ)
    (hmetric : ∀ x u v : V,
      (gaugePullbackMetric g Φ.symm).inner x u v =
        (gaugePullbackMetric h Ψ.symm).inner x u v) (x u v : V) :
    g.inner x u v = h.inner x u v := by
  have hΦΨ : Φ = Ψ := Diffeomorph.ext (congrFun hmap)
  subst Ψ
  exact (gaugePullbackMetric_symm_recover g Φ x u v).symm.trans
    ((hmetric (Φ x) (fderiv ℝ (Φ : V → V) x u) (fderiv ℝ (Φ : V → V) x v)).trans
      (gaugePullbackMetric_symm_recover h Φ x u v))

end PoincareConjecture.M35.Uniqueness
