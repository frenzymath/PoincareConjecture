import PoincareConjecture.Proofs.M35.RadialGauge.InverseMixedDerivative
import PoincareConjecture.Proofs.M35.RadialGauge.NativeLieCoordinates
import PoincareConjecture.Proofs.M35.Sec12_4_Uniqueness.GaugePullbackMetric











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M35.RadialGauge

open Uniqueness DeTurckNative

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

private theorem bilinear_time_partial
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {C : ℝ → E → E →L[ℝ] E →L[ℝ] ℝ} {t : ℝ} {y : E}
    {L : ℝ × E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ} {A : E → E → ℝ}
    (hC : HasFDerivAt (Function.uncurry C) L (t, y))
    (hsource : ∀ c d : E, HasDerivAt (fun s => C s y c d) (A c d) t)
    (c d : E) : L (1, 0) c d = A c d := by
  have htime : HasDerivAt (fun s => C s y) (L (1, 0)) t := by
    simpa only [Function.comp_def, Function.uncurry_def, id_eq] using
      hC.comp_hasDerivAt t ((hasDerivAt_id t).prodMk (hasDerivAt_const t y))
  have hfirst : HasDerivAt (fun s => C s y c) (L (1, 0) c) t := by
    simpa only [map_zero, add_zero] using htime.clm_apply (hasDerivAt_const t c)
  have h := hfirst.clm_apply (hasDerivAt_const t d)
  have hd : HasDerivAt (fun s => C s y c d) (L (1, 0) c d) t := by
    simpa only [Function.comp_def, Function.uncurry_def, id_eq,
      map_zero, add_zero] using! h
  exact hd.unique (hsource c d)



theorem inverse_pullback_metric_pair_hasDerivAt
    {g : ℝ → RiemannianMetric n V}
    {Φ : ℝ → Diffeomorph (𝓡 n) (𝓡 n) V V ∞} {J : Set ℝ} (hJ : IsOpen J)
    (hΦ : ContDiffOn ℝ 2 (fun p : ℝ × V => Φ p.1 p.2) (J ×ˢ univ))
    {t : ℝ} (ht : t ∈ J) {W : V → V} (hW : ContDiff ℝ ∞ W)
    (hvelocity : ∀ z : V, HasDerivAt (fun s => Φ s z) (-W (Φ t z)) t)
    (x u v : V)
    (hg : ContDiffAt ℝ 1
      (fun p : ℝ × V => (g p.1).euclideanCoefficients p.2) (t, (Φ t).symm x))
    {A : V → V → ℝ}
    (hsource : ∀ a b : V, HasDerivAt (fun s => (g s).inner ((Φ t).symm x) a b)
      (A a b) t)
    (K : LeviCivitaData (gaugePullbackMetric (g t) (Φ t).symm)) :
    HasDerivAt (fun s => (gaugePullbackMetric (g s) (Φ s).symm).inner x u v)
      (A (fderiv ℝ ((Φ t).symm : V → V) x u)
          (fderiv ℝ ((Φ t).symm : V → V) x v) +
        metricLieDerivative K W x u v) t := by
  let q : ℝ → V → V := fun s => (Φ s).symm
  let C (s : ℝ) := (g s).euclideanCoefficients
  let L := fderiv ℝ (Function.uncurry C) (t, q t x)
  let a := fderiv ℝ (q t) x u
  let b := fderiv ℝ (q t) x v
  let z := fderiv ℝ (q t) x (W x)
  have hqs : ContDiff ℝ ∞ (q t) := contMDiff_iff_contDiff.mp (Φ t).symm.contMDiff
  have hq := (hqs.differentiable (by simp) x).hasFDerivAt
  have hdq := ((hqs.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x).hasFDerivAt
  have hCt : HasFDerivAt (C t) (fderiv ℝ (C t) (q t x)) (q t x) :=
    ((g t).contDiffAt_euclideanCoefficients (q t x)).differentiableAt (by simp) |>.hasFDerivAt
  have hC : HasFDerivAt (Function.uncurry C) L (t, q t x) :=
    hg.differentiableAt one_ne_zero |>.hasFDerivAt
  have hqt : HasDerivAt (fun s => q s x) z t := by
    have h := diffeomorph_family_symm_hasDerivAt hJ (hΦ.of_le (by norm_num)) ht
      (hvelocity ((Φ t).symm x))
    simpa only [(Φ t).apply_symm_apply, map_neg, neg_neg] using h
  have hCtime := hC.comp_hasDerivAt t ((hasDerivAt_id t).prodMk hqt)
  have hut := diffeomorph_family_symm_fderiv_hasDerivAt hJ hΦ ht
    (hW.differentiable (by simp)) hvelocity x u
  have hvt := diffeomorph_family_symm_fderiv_hasDerivAt hJ hΦ ht
    (hW.differentiable (by simp)) hvelocity x v
  have hcurve : HasDerivAt
      (fun s => (gaugePullbackMetric (g s) (Φ s).symm).inner x u v)
      (L (1, z) a b + C t (q t x)
          (fderiv ℝ (fderiv ℝ (q t)) x (W x) u + fderiv ℝ (q t) x (fderiv ℝ W x u)) b +
        C t (q t x) a
          (fderiv ℝ (fderiv ℝ (q t)) x (W x) v + fderiv ℝ (q t) x (fderiv ℝ W x v))) t := by
    have h := (hCtime.clm_apply hut).clm_apply hvt
    simpa only [gaugePullbackMetric_inner, RiemannianMetric.euclideanCoefficients,
      q, C, a, b, z, add_apply, ContinuousLinearMap.comp_apply, add_assoc,
      Function.comp_def, Function.uncurry_def, id_eq] using! h
  have hsource' (c d : V) : L (1, 0) c d = A c d := by
    apply bilinear_time_partial hC (fun a b => ?_) c d
    simpa only [C, q, RiemannianMetric.euclideanCoefficients] using! hsource a b
  have hspace : L ∘L ContinuousLinearMap.inr ℝ ℝ V = fderiv ℝ (C t) (q t x) :=
    (hC.comp (q t x) (hasFDerivAt_prodMk_right t (q t x))).unique hCt
  have hsplit : L (1, z) = L (1, 0) + fderiv ℝ (C t) (q t x) z := by
    rw [show ((1, z) : ℝ × V) = (1, 0) + (0, z) by ext <;> simp, map_add]
    congr 1
    exact congrArg (fun A : V →L[ℝ] V →L[ℝ] V →L[ℝ] ℝ => A z) hspace
  have hspatial :
      fderiv ℝ (fun y => (gaugePullbackMetric (g t) (Φ t).symm).inner y u v) x (W x) =
        fderiv ℝ (C t) (q t x) z a b +
          C t (q t x) (fderiv ℝ (fderiv ℝ (q t)) x (W x) u) b +
          C t (q t x) a (fderiv ℝ (fderiv ℝ (q t)) x (W x) v) := by
    have h := ((hCt.comp x hq).clm_apply
      (hdq.clm_apply (hasFDerivAt_const u x))).clm_apply
        (hdq.clm_apply (hasFDerivAt_const v x))
    simp only [Function.comp_def] at h
    have heq : (fun y => (gaugePullbackMetric (g t) (Φ t).symm).inner y u v) =
        fun y => C t (q t y) (fderiv ℝ (q t) y u) (fderiv ℝ (q t) y v) := by
      funext y
      exact gaugePullbackMetric_inner (g t) (Φ t).symm y u v
    rw [heq, h.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
      add_apply, zero_apply, map_zero, zero_add, a, b, z, add_assoc]
    ring
  apply hcurve.congr_deriv
  rw [hsplit, add_apply, add_apply, hsource',
    metricLieDerivative_euclidean_pair K hW, hspatial,
    gaugePullbackMetric_inner, gaugePullbackMetric_inner]
  simp only [map_add, add_apply, C, q, a, b, RiemannianMetric.euclideanCoefficients]
  ac_rfl

end PoincareConjecture.M35.RadialGauge
