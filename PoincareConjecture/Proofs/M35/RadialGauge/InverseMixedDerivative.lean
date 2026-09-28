import PoincareConjecture.Proofs.M35.RadialGauge.DiffeomorphInverseTime
import PoincareConjecture.Proofs.M03.Existence.ConjugatorLieDerivativeNative










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

private theorem spatial_fderiv_time_as_joint
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × E → F} {t : ℝ} {x : E} (hf : ContDiffAt ℝ 2 f (t, x)) (v : E) :
    HasDerivAt (fun s => fderiv ℝ (fun z => f (s, z)) x v)
      (fderiv ℝ (fderiv ℝ f) (t, x) (1, 0) (0, v)) t := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ f) (t, x) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hlocal : ∀ᶠ q in 𝓝 (t, x), DifferentiableAt ℝ f q :=
    (hf.eventually (by norm_num)).mono fun _ h => h.differentiableAt two_ne_zero
  have htx : ContinuousAt (fun s : ℝ => (s, x)) t := by fun_prop
  have hDtime := (hfd.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))).clm_apply
      (hasDerivAt_const t ((0, v) : ℝ × E))
  have hspatial : (fun s => fderiv ℝ (fun z => f (s, z)) x v) =ᶠ[𝓝 t]
      (fun s => fderiv ℝ f (s, x) (0, v)) := by
    filter_upwards [htx hlocal] with s hs
    change fderiv ℝ (f ∘ Prod.mk s) x v = _
    rw [(hs.hasFDerivAt.comp x (hasFDerivAt_prodMk_right s x)).fderiv]
    rfl
  have hh : HasDerivAt (fun s => fderiv ℝ f (s, x) (0, v))
      (fderiv ℝ (fderiv ℝ f) (t, x) (1, 0) (0, v)) t := by
    simpa only [map_zero, add_zero, Function.comp_apply, id_eq] using hDtime
  exact hh.congr_of_eventuallyEq hspatial

private theorem source_fderiv_as_joint
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × E → F} {H : E → F} {t : ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f (t, x))
    (htime : ∀ᶠ z in 𝓝 x, HasDerivAt (fun s => f (s, z)) (H z) t) (v : E) :
    fderiv ℝ H x v = fderiv ℝ (fderiv ℝ f) (t, x) (0, v) (1, 0) := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ f) (t, x) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hlocal : ∀ᶠ q in 𝓝 (t, x), DifferentiableAt ℝ f q :=
    (hf.eventually (by norm_num)).mono fun _ h => h.differentiableAt two_ne_zero
  have htz : ContinuousAt (fun z : E => (t, z)) x := by fun_prop
  have hsource : (fun z => fderiv ℝ f (t, z) (1, 0)) =ᶠ[𝓝 x] H := by
    filter_upwards [htz hlocal, htime] with z hz ht
    have hd := hz.hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t z))
    exact hd.unique ht
  have hspaceTime : HasFDerivAt (fun z => fderiv ℝ f (t, z) (1, 0))
      (((fderiv ℝ (fderiv ℝ f) (t, x)).comp
        (ContinuousLinearMap.inr ℝ ℝ E)).flip (1, 0)) x := by
    have h := (hfd.hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)).clm_apply
      (hasFDerivAt_const ((1, 0) : ℝ × E) x)
    simpa only [ContinuousLinearMap.comp_zero, zero_add, Function.comp_def] using h
  have hderivs := (hspaceTime.congr_of_eventuallyEq hsource.symm).fderiv
  exact congrArg (fun A : E →L[ℝ] F => A v) hderivs

private theorem spatial_fderiv_time_of_source
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × E → F} {H : E → F} {t : ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f (t, x))
    (htime : ∀ᶠ z in 𝓝 x, HasDerivAt (fun s => f (s, z)) (H z) t) (v : E) :
    HasDerivAt (fun s => fderiv ℝ (fun z => f (s, z)) x v) (fderiv ℝ H x v) t := by
  have hmixed := hf.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField])
  apply (spatial_fderiv_time_as_joint hf v).congr_deriv
  calc
    fderiv ℝ (fderiv ℝ f) (t, x) (1, 0) (0, v) =
        fderiv ℝ (fderiv ℝ f) (t, x) (0, v) (1, 0) := hmixed.eq (1, 0) (0, v)
    _ = _ := (source_fderiv_as_joint hf htime v).symm



theorem diffeomorph_family_symm_fderiv_hasDerivAt
    {Φ : ℝ → Diffeomorph (𝓡 n) (𝓡 n) V V ∞} {J : Set ℝ} (hJ : IsOpen J)
    (hc : ContDiffOn ℝ 2 (fun p : ℝ × V => Φ p.1 p.2) (J ×ˢ univ))
    {t : ℝ} (ht : t ∈ J) {W : V → V} (hW : Differentiable ℝ W)
    (htime : ∀ z : V, HasDerivAt (fun s => Φ s z) (-W (Φ t z)) t)
    (x v : V) :
    HasDerivAt (fun s => fderiv ℝ ((Φ s).symm : V → V) x v)
      (fderiv ℝ (fderiv ℝ ((Φ t).symm : V → V)) x (W x) v +
        fderiv ℝ ((Φ t).symm : V → V) x (fderiv ℝ W x v)) t := by
  let q : ℝ → V → V := fun s => (Φ s).symm
  have hqs : ContDiff ℝ ∞ (q t) := contMDiff_iff_contDiff.mp (Φ t).symm.contMDiff
  have hq : ContDiffAt ℝ 2 (Function.uncurry q) (t, x) :=
    diffeomorph_family_symm_contDiffAt_order (k := 2) (by norm_num) hJ hc ht
  have hqtime (z : V) : HasDerivAt (fun s => q s z) (fderiv ℝ (q t) z (W z)) t := by
    have h := diffeomorph_family_symm_hasDerivAt hJ (hc.of_le (by norm_num)) ht
      (htime ((Φ t).symm z))
    simpa only [(Φ t).apply_symm_apply, map_neg, neg_neg] using h
  have hd := ((hqs.fderiv_right (m := ∞) (by simp)).differentiable
    (by simp) x).hasFDerivAt.clm_apply (hW x).hasFDerivAt
  have h := spatial_fderiv_time_of_source hq
    (Filter.Eventually.of_forall hqtime) v
  have heq : fderiv ℝ (fun z => fderiv ℝ (q t) z (W z)) x v =
      fderiv ℝ (fderiv ℝ (q t)) x (W x) v +
        fderiv ℝ (q t) x (fderiv ℝ W x v) := by
    rw [hd.fderiv]
    change fderiv ℝ (q t) x (fderiv ℝ W x v) +
      fderiv ℝ (fderiv ℝ (q t)) x v (W x) = _
    rw [(hqs.contDiffAt.isSymmSndFDerivAt
      (by rw [minSmoothness_of_isRCLikeNormedField]
          exact WithTop.coe_le_coe.mpr le_top)).eq v (W x)]
    exact add_comm _ _
  rw [heq] at h
  exact h

end PoincareConjecture.M35.RadialGauge
