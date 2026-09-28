import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerAnnularGluing
import PoincareConjecture.Proofs.M58.Cor18_28_PolarDerivatives
import PoincareConjecture.Proofs.M60.Mathlib.NullSphere
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter MeasureTheory Real
open scoped Topology Manifold ContDiff Pointwise

noncomputable section

namespace PoincareConjecture.M60

open Proofs.M58

private def annularTheta (R d : ℝ) (z : LoopPlane) : ℝ :=
  smoothTransition ((‖z‖ - (R - d)) / (2 * d))

private theorem annularTheta_diff (R d : ℝ) {z : LoopPlane} (hz : z ≠ 0) :
    DifferentiableAt ℝ (annularTheta R d) z := by
  have hn := (contDiffAt_norm ℝ hz).differentiableAt one_ne_zero
  apply ((smoothTransition.contDiff (n := ⊤)).differentiable (by simp) _).comp z
  simpa only [div_eq_mul_inv] using (hn.sub_const (R - d)).mul_const ((2 * d)⁻¹)

private theorem annularTheta_derivative_bound :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ R d : ℝ, 0 < d → ∀ z : LoopPlane, z ≠ 0 →
      R - d < ‖z‖ → ‖z‖ < R + d → ‖fderiv ℝ (annularTheta R d) z‖ ≤ H / (2 * d) := by
  obtain ⟨H, hH⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((smoothTransition.contDiff (n := ⊤)).continuous_deriv (by simp)).continuousOn
  refine ⟨max H 0, le_max_right _ _, ?_⟩
  intro R d hd z hz hlo hhi
  let x := (‖z‖ - (R - d)) / (2 * d)
  have hx : x ∈ Icc (0 : ℝ) 1 :=
    ⟨(div_nonneg (by linarith only [hlo]) (by positivity)),
      (div_le_one (by positivity)).mpr (by linarith only [hhi])⟩
  have hs : |deriv smoothTransition x| ≤ max H 0 := (hH x hx).trans (le_max_left _ _)
  have hn := (contDiffAt_norm ℝ hz).differentiableAt one_ne_zero
  have hlin : HasFDerivAt (fun w : LoopPlane => (‖w‖ - (R - d)) / (2 * d))
      ((2 * d)⁻¹ • fderiv ℝ (fun w : LoopPlane => ‖w‖) z) z := by
    simpa only [div_eq_mul_inv, mul_comm] using
      (hn.hasFDerivAt.sub_const (R - d)).const_mul ((2 * d)⁻¹)
  have hsmooth := ((smoothTransition.contDiff (n := ⊤)).differentiable (by simp) x).hasDerivAt
  have hder := (hsmooth.comp_hasFDerivAt z hlin).fderiv
  change fderiv ℝ (annularTheta R d) z = _ at hder
  rw [hder, norm_smul, norm_smul, Real.norm_eq_abs, norm_fderiv_norm hn,
    mul_one, Real.norm_of_nonneg (inv_nonneg.mpr (by positivity))]
  simpa only [div_eq_mul_inv] using
    mul_le_mul_of_nonneg_right hs (inv_nonneg.mpr (by positivity : 0 ≤ 2 * d))

private theorem annularTheta_angular (R d : ℝ) {r : ℝ} (hr : 0 < r) (t : ℝ) :
    fderiv ℝ (annularTheta R d) (r • angularPoint t) (angularVector t) = 0 := by
  have hnorm (s : ℝ) : ‖r • angularPoint s‖ = r := by
    rw [norm_smul, Real.norm_of_nonneg hr.le, norm_angularPoint, mul_one]
  have hz : r • angularPoint t ≠ 0 := norm_pos_iff.mp (by rwa [hnorm])
  have hδ := (hasDerivAt_angularPoint t).const_smul r
  have hder := ((annularTheta_diff R d hz).hasFDerivAt.comp_hasDerivAt t hδ).deriv
  have heq : (fun s => annularTheta R d (r • angularPoint s)) =
      fun _ : ℝ => smoothTransition ((r - (R - d)) / (2 * d)) := by
    funext s
    simp only [annularTheta, hnorm]
  change deriv (fun s => annularTheta R d (r • angularPoint s)) t = _ at hder
  rw [heq, deriv_const] at hder
  rw [map_smul, smul_eq_mul] at hder
  exact (mul_eq_zero.mp hder.symm).resolve_left hr.ne'

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

open scoped Bundle in
private theorem annular_area_frame (g : RiemannianMetric n M)
    (F : LoopPlane → M) (z : LoopPlane) (t : ℝ) :
    m60AreaDensity g F z ≤
      g.tangentNorm (F z) (mfderiv (𝓡 2) (𝓡 n) F z (angularPoint t)) *
      g.tangentNorm (F z) (mfderiv (𝓡 2) (𝓡 n) F z (angularVector t)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let D := mfderiv (𝓡 2) (𝓡 n) F z
  let e := EuclideanSpace.basisFun (Fin 2) ℝ
  let u := D (e 0)
  let v := D (e 1)
  have harea : m60AreaDensity g F z = twoVectorArea u v := by
    unfold m60AreaDensity m60AreaGram twoVectorArea
    dsimp only
    erw [Matrix.det_fin_two]
    change sqrt (max 0 (inner ℝ u u * inner ℝ v v - inner ℝ u v * inner ℝ v u)) = _
    rw [real_inner_comm v u, pow_two]
  have hrep (w : LoopPlane) : D w = w 0 • u + w 1 • v := by
    have hw : w = w 0 • e 0 + w 1 • e 1 := by
      simpa only [e, Fin.sum_univ_two, EuclideanSpace.basisFun_repr] using (e.sum_repr w).symm
    calc
      D w = D (w 0 • e 0 + w 1 • e 1) := congrArg D hw
      _ = _ := by rw [map_add, map_smul, map_smul]
  have hframe : twoVectorArea (D (angularPoint t)) (D (angularVector t)) =
      m60AreaDensity g F z := by
    rw [hrep, hrep]
    change twoVectorArea (cos t • u + sin t • v) (-sin t • u + cos t • v) = _
    rw [twoVectorArea_change]
    have hdet : cos t * cos t - sin t * -sin t = 1 := by
      nlinarith only [cos_sq_add_sin_sq t]
    rw [hdet, abs_one, one_mul, ← harea]
  exact hframe ▸ twoVectorArea_le (D (angularPoint t)) (D (angularVector t))

open scoped Bundle in

theorem suAnnularBlend_density_bound (g : RiemannianMetric n M) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ (C : ℝ × (M × M) → M) (U : Set (M × M)),
      (∀ x ∈ Icc (0 : ℝ) 1 ×ˢ U,
        MDifferentiableAt (𝓘(ℝ, ℝ).prod ((𝓡 n).prod (𝓡 n))) (𝓡 n) C x) →
      ∀ A B L : ℝ, 0 ≤ A → 0 ≤ B → 0 ≤ L →
      (∀ x ∈ Icc (0 : ℝ) 1 ×ˢ U, g.tangentNorm (C x)
        (mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 n).prod (𝓡 n))) (𝓡 n) C x (1, 0, 0)) ≤ A) →
      (∀ x ∈ Icc (0 : ℝ) 1 ×ˢ U,
        ∀ v : TangentSpace (𝓡 n) x.2.1, ∀ w : TangentSpace (𝓡 n) x.2.2,
          g.tangentNorm (C x)
            (mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 n).prod (𝓡 n))) (𝓡 n) C x (0, v, w)) ≤
              B * (g.tangentNorm x.2.1 v + g.tangentNorm x.2.2 w)) →
      ∀ (f a : LoopPlane → M), ContMDiff (𝓡 2) (𝓡 n) 1 f →
        ContMDiff (𝓡 2) (𝓡 n) 1 a → ∀ R d : ℝ, 0 < d →
      ∀ z : LoopPlane, z ≠ 0 → R - d < ‖z‖ → ‖z‖ < R + d → (f z, a z) ∈ U →
      (∀ w : LoopPlane,
        g.tangentNorm (f z) (mfderiv (𝓡 2) (𝓡 n) f z w) +
          g.tangentNorm (a z) (mfderiv (𝓡 2) (𝓡 n) a z w) ≤ L * ‖w‖) →
      m60AreaDensity g (suAnnularBlend C f a R d) z ≤
        (H / (2 * d) * A + B * L) * (B * L) := by
  obtain ⟨H, hH, hprofile⟩ := annularTheta_derivative_bound
  refine ⟨H, hH, ?_⟩
  intro C U hC A B L hA hB hL htime hspace f a hf ha R d hd z hz hlo hhi hpairs hmaps
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let θ := annularTheta R d
  let x := (θ z, f z, a z)
  let D := mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 n).prod (𝓡 n))) (𝓡 n) C x
  let F := fun y : LoopPlane => C (θ y, f y, a y)
  have hx : x ∈ Icc (0 : ℝ) 1 ×ˢ U :=
    ⟨⟨smoothTransition.nonneg _, smoothTransition.le_one _⟩, hpairs⟩
  have hθ : DifferentiableAt ℝ θ z := annularTheta_diff R d hz
  have hfm := (hf z).mdifferentiableAt one_ne_zero
  have ham := (ha z).mdifferentiableAt one_ne_zero
  have hin := hθ.mdifferentiableAt.prodMk (hfm.prodMk ham)
  have hder (w : LoopPlane) : mfderiv (𝓡 2) (𝓡 n) F z w =
      D (fderiv ℝ θ z w, mfderiv (𝓡 2) (𝓡 n) f z w, mfderiv (𝓡 2) (𝓡 n) a z w) := by
    have h := mfderiv_comp_apply z (hC x hx) hin w
    erw [mfderiv_prodMk hθ.mdifferentiableAt (hfm.prodMk ham),
      mfderiv_prodMk hfm ham, mfderiv_eq_fderiv] at h
    exact h
  have heq : suAnnularBlend C f a R d =ᶠ[𝓝 z] F := by
    have hnear : ∀ᶠ y in 𝓝 z, R - d < ‖y‖ ∧ ‖y‖ < R + d :=
      ((isOpen_lt continuous_const continuous_norm).inter
        (isOpen_lt continuous_norm continuous_const)).mem_nhds ⟨hlo, hhi⟩
    filter_upwards [hnear] with y hy
    simp only [suAnnularBlend, if_neg (not_le.mpr hy.2), if_neg (not_le.mpr hy.1)]
    rfl
  rw [m60AreaDensity_congr_of_eventuallyEq g heq]
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hunit : ‖‖z‖⁻¹ • z‖ = 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le), inv_mul_cancel₀ hr.ne']
  obtain ⟨t, _, ht⟩ := exists_angularPoint ⟨‖z‖⁻¹ • z, hunit⟩
  have hpolar : z = ‖z‖ • angularPoint t := by rw [ht, smul_inv_smul₀ hr.ne']
  have hvnorm : ‖angularVector t‖ = 1 := by
    simp [angularVector, EuclideanSpace.norm_eq, Fin.sum_univ_two, sin_sq_add_cos_sq]
  have hθu : |fderiv ℝ θ z (angularPoint t)| ≤ H / (2 * d) := by
    have h := (fderiv ℝ θ z).le_opNorm (angularPoint t)
    rw [norm_angularPoint, mul_one] at h
    exact h.trans (hprofile R d hd z hz hlo hhi)
  have hθv : fderiv ℝ θ z (angularVector t) = 0 := by
    conv_lhs => rw [hpolar]
    exact annularTheta_angular R d hr t
  have hrad : g.tangentNorm (F z)
      (mfderiv (𝓡 2) (𝓡 n) F z (angularPoint t)) ≤ H / (2 * d) * A + B * L := by
    rw [hder]
    change ‖D (fderiv ℝ θ z (angularPoint t),
      mfderiv (𝓡 2) (𝓡 n) f z (angularPoint t),
      mfderiv (𝓡 2) (𝓡 n) a z (angularPoint t))‖ ≤ _
    have hsplit : (fderiv ℝ θ z (angularPoint t),
        mfderiv (𝓡 2) (𝓡 n) f z (angularPoint t),
        mfderiv (𝓡 2) (𝓡 n) a z (angularPoint t)) =
      fderiv ℝ θ z (angularPoint t) • ((1, 0, 0) :
        TangentSpace (𝓘(ℝ, ℝ).prod ((𝓡 n).prod (𝓡 n))) x) +
      (0, mfderiv (𝓡 2) (𝓡 n) f z (angularPoint t),
        mfderiv (𝓡 2) (𝓡 n) a z (angularPoint t)) := by simp
    rw [hsplit, map_add, map_smul]
    apply (norm_add_le _ _).trans
    apply add_le_add
    · rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul hθu (htime x hx) (norm_nonneg _)
        (div_nonneg hH (by positivity))
    · have hmap := hmaps (angularPoint t)
      rw [norm_angularPoint, mul_one] at hmap
      exact (hspace x hx _ _).trans (mul_le_mul_of_nonneg_left hmap hB)
  have hang : g.tangentNorm (F z)
      (mfderiv (𝓡 2) (𝓡 n) F z (angularVector t)) ≤ B * L := by
    rw [hder, hθv]
    have hmap := hmaps (angularVector t)
    rw [hvnorm, mul_one] at hmap
    exact (hspace x hx _ _).trans (mul_le_mul_of_nonneg_left hmap hB)
  exact (annular_area_frame g F z t).trans
    (mul_le_mul hrad hang (by
      change 0 ≤ ‖mfderiv (𝓡 2) (𝓡 n) F z (angularVector t)‖
      exact norm_nonneg _) (by positivity))

private theorem annular_volume {R d : ℝ} (hd : 0 < d) (hRd : d < R) :
    volume.real (ball (0 : LoopPlane) (R + d) \ closedBall 0 (R - d)) = 4 * π * R * d := by
  have hsub : closedBall (0 : LoopPlane) (R - d) ⊆ ball 0 (R + d) :=
    closedBall_subset_ball (by linarith only [hd])
  rw [measureReal_sdiff hsub measurableSet_closedBall (measure_ball_lt_top.ne),
    Measure.real, Measure.real, EuclideanSpace.volume_ball_fin_two,
    EuclideanSpace.volume_closedBall_fin_two, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (by linarith only [hd, hRd] : 0 ≤ R + d),
    ENNReal.toReal_ofReal (by linarith only [hRd] : 0 ≤ R - d),
    ENNReal.toReal_ofReal pi_pos.le]
  ring

theorem suAnnular_area_estimate (g : RiemannianMetric n M)
    {F : LoopPlane → M} (hF : ContMDiff (𝓡 2) (𝓡 n) 1 F)
    {R d H A B L : ℝ} (hd : 0 < d) (hRd : d < R)
    (hbound : ∀ z ∈ ball (0 : LoopPlane) (R + d) \ closedBall 0 (R - d),
      m60AreaDensity g F z ≤ (H / (2 * d) * A + B * L) * (B * L)) :
    IntegrableOn (m60AreaDensity g F)
      (ball (0 : LoopPlane) (R + d) \ closedBall 0 (R - d)) ∧
    (∫ z in ball (0 : LoopPlane) (R + d) \ closedBall 0 (R - d), m60AreaDensity g F z) ≤
      4 * π * R * (H * A / 2 * (B * L) + d * (B * L) ^ 2) := by
  let S := ball (0 : LoopPlane) (R + d) \ closedBall 0 (R - d)
  have hS : MeasurableSet S := measurableSet_ball.diff measurableSet_closedBall
  have hi : IntegrableOn (m60AreaDensity g F) S :=
    ((m60AreaDensity_continuous g hF).continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : LoopPlane) (R + d))).mono_set
        (fun _ hz => ball_subset_closedBall hz.1)
  have hfin : volume S ≠ ⊤ :=
    (lt_of_le_of_lt (measure_mono sdiff_subset) measure_ball_lt_top).ne
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ _ in S, (H / (2 * d) * A + B * L) * (B * L) :=
      setIntegral_mono_on hi (integrableOn_const hfin) hS hbound
    _ = _ := by
      rw [setIntegral_const, smul_eq_mul, annular_volume hd hRd]
      field_simp

theorem suSphereArea_rescaled (g : RiemannianMetric n M)
    {f : UnitTwoSphere → M} (hf : ContMDiff (𝓡 2) (𝓡 n) 1 f)
    (c : UnitTwoSphere) {s : ℝ} (hs : 0 < s) :
    Integrable (m60AreaDensity g (fun z => f ((chartAt LoopPlane c).symm (s • z)))) ∧
      (∫ z : LoopPlane, m60AreaDensity g (fun z => f ((chartAt LoopPlane c).symm (s • z))) z) =
        m60SphereArea g f := by
  obtain ⟨hi, harea⟩ := suSphereArea_chart g hf c
  have hset : s • (univ : Set LoopPlane) = univ := by
    ext z
    constructor
    · exact fun _ => mem_univ z
    · intro _
      exact ⟨s⁻¹ • z, mem_univ _, smul_inv_smul₀ hs.ne' z⟩
  have h := m60AreaDensity_integrableOn_comp_smul g
    (f ∘ (chartAt LoopPlane c).symm) hs.ne' univ (by simpa only [hset, integrableOn_univ] using hi)
  have ha := m60AreaIntegral_comp_smul g (f ∘ (chartAt LoopPlane c).symm) hs univ
  rw [hset, setIntegral_univ, setIntegral_univ] at ha
  exact ⟨by simpa only [integrableOn_univ, Function.comp_apply] using h, ha.trans harea⟩

theorem suAnnularBlend_area_bookkeeping (g : RiemannianMetric n M)
    (C : ℝ × (M × M) → M) (f a : LoopPlane → M) {R d E : ℝ}
    (hd : 0 < d)
    (hf : Integrable (m60AreaDensity g f))
    (ha : IntegrableOn (m60AreaDensity g a) (ball (0 : LoopPlane) R))
    (hB : Integrable (m60AreaDensity g (suAnnularBlend C f a R d)))
    (hcollar : (∫ z in ball (0 : LoopPlane) (R + d) \ closedBall 0 (R - d),
      m60AreaDensity g (suAnnularBlend C f a R d) z) ≤ E) :
    (∫ z, m60AreaDensity g (suAnnularBlend C f a R d) z) ≤
      (∫ z, m60AreaDensity g f z) - (∫ z in ball (0 : LoopPlane) R, m60AreaDensity g f z) +
        (∫ z in ball (0 : LoopPlane) R, m60AreaDensity g a z) + E := by
  let B := suAnnularBlend C f a R d
  have hi : (∫ z in closedBall (0 : LoopPlane) (R - d), m60AreaDensity g B z) =
      ∫ z in closedBall (0 : LoopPlane) (R - d), m60AreaDensity g a z := by
    rw [setIntegral_congr_set (haar_ball_ae_eq_closedBall volume (0 : LoopPlane) (R - d)).symm,
      setIntegral_congr_set (haar_ball_ae_eq_closedBall volume (0 : LoopPlane) (R - d)).symm]
    apply setIntegral_congr_fun measurableSet_ball
    intro z hz
    apply m60AreaDensity_congr_of_eventuallyEq
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw
    exact suAnnularBlend_inner C f a hd (mem_ball_zero_iff.mp hw).le
  have ho : (∫ z in (closedBall (0 : LoopPlane) (R + d))ᶜ, m60AreaDensity g B z) =
      ∫ z in (closedBall (0 : LoopPlane) (R + d))ᶜ, m60AreaDensity g f z := by
    apply setIntegral_congr_fun measurableSet_closedBall.compl
    intro z hz
    apply m60AreaDensity_congr_of_eventuallyEq
    filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds hz] with w hw
    exact suAnnularBlend_outer C f a (le_of_lt (not_le.mp (by
      simpa only [mem_compl_iff, mem_closedBall_zero_iff] using hw)))
  have hm : (∫ z in closedBall (0 : LoopPlane) (R + d) \ closedBall 0 (R - d),
      m60AreaDensity g B z) ≤ E := by
    have hsets : closedBall (0 : LoopPlane) (R + d) \ closedBall 0 (R - d) =ᵐ[volume]
        ball 0 (R + d) \ closedBall 0 (R - d) :=
      ((haar_ball_ae_eq_closedBall volume (0 : LoopPlane) (R + d)).symm).diff EventuallyEq.rfl
    rw [setIntegral_congr_set hsets]
    exact hcollar
  have hia : (∫ z in closedBall (0 : LoopPlane) (R - d), m60AreaDensity g a z) ≤
      ∫ z in ball (0 : LoopPlane) R, m60AreaDensity g a z :=
    setIntegral_mono_set ha (Eventually.of_forall (m60AreaDensity_nonneg g a))
      (Eventually.of_forall fun _ hz => closedBall_subset_ball (by linarith only [hd]) hz)
  have hof : (∫ z in (closedBall (0 : LoopPlane) (R + d))ᶜ, m60AreaDensity g f z) ≤
      ∫ z in (ball (0 : LoopPlane) R)ᶜ, m60AreaDensity g f z :=
    setIntegral_mono_set hf.integrableOn (Eventually.of_forall (m60AreaDensity_nonneg g f))
      (Eventually.of_forall fun _ hz => fun hb => hz
        (ball_subset_closedBall ((ball_subset_ball (by linarith only [hd])) hb)))
  have hsplit := setIntegral_sdiff
    (s := closedBall (0 : LoopPlane) (R + d)) (t := closedBall (0 : LoopPlane) (R - d))
    measurableSet_closedBall hB.integrableOn
    (closedBall_subset_closedBall (show R - d ≤ R + d by linarith only [hd]))
  have htotal := integral_add_compl (μ := volume)
    (measurableSet_closedBall (x := (0 : LoopPlane)) (ε := R + d)) hB
  have hftotal := integral_add_compl (μ := volume)
    (measurableSet_ball (x := (0 : LoopPlane)) (ε := R)) hf
  change (∫ z in closedBall (0 : LoopPlane) (R + d) \ closedBall 0 (R - d),
    m60AreaDensity g B z) = _ at hsplit
  change (∫ z in closedBall (0 : LoopPlane) (R + d), m60AreaDensity g B z) +
    (∫ z in (closedBall (0 : LoopPlane) (R + d))ᶜ, m60AreaDensity g B z) = _ at htotal
  rw [hi] at hsplit
  rw [ho] at htotal
  linarith

end PoincareConjecture.M60
