import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerDilation
import PoincareConjecture.Proofs.M03.Existence.DeTurckDomainRegularityNative

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter Metric
open scoped Topology SchwartzMap ContDiff InnerProductSpace LineDeriv

namespace PoincareConjecture

open EuclideanMollificationNative DeTurckDomainRegularityNative

private theorem m65Dilation_indicator_coe {r : ℝ} (hr : 1 / 2 ≤ r) (hr1 : r ≤ 1)
    (w : Lp ℝ 2 (volume : Measure LoopPlane)) (f : LoopPlane → ℝ)
    (hw : w =ᵐ[volume] loopDiskSet.indicator f) :
    m65DiskDilationL2 r hr w =ᵐ[volume.restrict loopDiskSet] fun z => f (r • z) := by
  have hrpos : 0 < r := lt_of_lt_of_le (by norm_num) hr
  have hcomp : (fun z => w (r • z)) =ᵐ[volume.restrict loopDiskSet]
      fun z => loopDiskSet.indicator f (r • z) := ae_restrict_of_ae
    ((Measure.quasiMeasurePreserving_smul volume hrpos.ne').ae hw)
  filter_upwards [m65DiskDilationL2_coe r hr w, hcomp,
    ae_restrict_mem (show MeasurableSet loopDiskSet from measurableSet_closedBall)]
    with z hz hc hdisk
  rw [hz, hc, indicator_of_mem]
  apply mem_closedBall_zero_iff.mpr
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hrpos]
  exact (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hdisk) hrpos.le).trans
    (by simpa only [mul_one] using hr1)

set_option maxHeartbeats 1600000 in

private theorem m65WeakTrace_approximate_at_scale
    {u : Lp ℝ 2 (volume.restrict loopDiskSet)}
    {d : Fin 2 → Lp ℝ 2 (volume.restrict loopDiskSet)}
    {b : Lp ℝ 2 (volume.restrict (Icc (-Real.pi) Real.pi))}
    (htrace : M65DiskWeakTrace u d b)
    (Zu : Lp ℝ 2 (volume : Measure LoopPlane))
    (Zd : Fin 2 → Lp ℝ 2 (volume : Measure LoopPlane))
    (hZu : Zu =ᵐ[volume] loopDiskSet.indicator (u : LoopPlane → ℝ))
    (hZd : ∀ i, Zd i =ᵐ[volume] loopDiskSet.indicator (d i : LoopPlane → ℝ))
    {r : ℝ} (hr : 1 / 2 ≤ r) (hr1 : r < 1) {eps : ℝ} (heps : 0 < eps) :
    ∃ (f : LoopPlane → ℝ) (A : Lp ℝ 2 (volume.restrict loopDiskSet))
      (B : Fin 2 → Lp ℝ 2 (volume.restrict loopDiskSet)),
      ContDiff ℝ ∞ f ∧ (A =ᵐ[volume.restrict loopDiskSet] f) ∧
      (∀ i, B i =ᵐ[volume.restrict loopDiskSet]
        fun z => fderiv ℝ f z (EuclideanSpace.basisFun (Fin 2) ℝ i)) ∧
      dist A (m65DiskDilationL2 r hr Zu) < eps ∧
      ∀ i, dist (B i) (r • m65DiskDilationL2 r hr (Zd i)) < eps := by
  have hrpos : 0 < r := lt_of_lt_of_le (by norm_num) hr
  let theta : ContDiffBump (0 : LoopPlane) :=
    { rIn := (r + 1) / 2
      rOut := (r + 3) / 4
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  let θ : 𝓢(LoopPlane, ℝ) := theta.hasCompactSupport.toSchwartzMap theta.contDiff
  have hsupport : tsupport θ ⊆ ball (0 : LoopPlane) 1 := by
    change tsupport theta ⊆ _
    rw [theta.tsupport_eq]
    apply closedBall_subset_ball
    dsimp only [theta]
    linarith
  have hθ (z : LoopPlane) (hz : z ∈ loopDiskSet) :
      θ (r • z) = 1 ∧ fderiv ℝ θ (r • z) = 0 := by
    have hnorm : ‖r • z‖ < theta.rIn := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hrpos]
      have hh := mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hz) hrpos.le
      dsimp only [theta]
      nlinarith
    have heq : (θ : LoopPlane → ℝ) =ᶠ[𝓝 (r • z)] fun _ => 1 :=
      theta.eventuallyEq_one_of_mem_ball (mem_ball_zero_iff.mpr hnorm)
    refine ⟨heq.eq_of_nhds, ?_⟩
    rw [heq.fderiv_eq]
    exact fderiv_const_apply (1 : ℝ)
  obtain ⟨U, D, hU, hD, hweak⟩ := m65WeakTrace_cutoff_global htrace θ hsupport
  let T := m65DiskDilationL2 r hr
  have hTU : T U = T Zu := by
    apply Lp.ext
    filter_upwards [m65Dilation_indicator_coe hr hr1.le U _ hU,
      m65Dilation_indicator_coe hr hr1.le Zu _ hZu,
      ae_restrict_mem (show MeasurableSet loopDiskSet from measurableSet_closedBall)]
      with z hu hz hdisk
    rw [hu, hz, (hθ z hdisk).1, one_mul]
  have hTD (i : Fin 2) : T (D i) = T (Zd i) := by
    apply Lp.ext
    filter_upwards [m65Dilation_indicator_coe hr hr1.le (D i) _ (hD i),
      m65Dilation_indicator_coe hr hr1.le (Zd i) _ (hZd i),
      ae_restrict_mem (show MeasurableSet loopDiskSet from measurableSet_closedBall)]
      with z hd hz hdisk
    rw [hd, hz, (hθ z hdisk).1, (hθ z hdisk).2]
    simp only [one_mul, zero_apply, zero_mul, add_zero]
  have hpair (i : Fin 2) (test : 𝓢(LoopPlane, ℝ)) :
      ⟪D i, test.toLp 2 volume⟫_ℝ = -(∫ z, U z *
        fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i)) := by
    have hh := hweak i test
    rw [inner_schwartz U] at hh
    exact hh
  let delta (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)
  have hdelta (k : ℕ) : 0 < delta k := by dsimp only [delta]; positivity
  have hdelta0 : Tendsto delta atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let f (k : ℕ) (z : LoopPlane) := mollify (hdelta k) U (r • z)
  let A (k : ℕ) := T (mollifyL2 (hdelta k) U)
  let B (k : ℕ) (i : Fin 2) := r • T (mollifyL2 (hdelta k) (D i))
  have hscale : ContDiff ℝ ∞ (fun z : LoopPlane => r • z) :=
    contDiff_id.const_smul r
  have hf (k : ℕ) : ContDiff ℝ ∞ (f k) := by
    exact (contDiff_mollify (hdelta k) U).comp hscale
  have hdf (k : ℕ) (z : LoopPlane) (i : Fin 2) :
      fderiv ℝ (f k) z (EuclideanSpace.basisFun (Fin 2) ℝ i) =
        r * mollify (hdelta k) (D i) (r • z) := by
    have hmd := (contDiff_mollify (hdelta k) U).differentiable (by simp)
    have hd := (hmd (r • z)).hasFDerivAt.comp z ((hasFDerivAt_id z).const_smul r)
    have hdeq : fderiv ℝ (f k) z =
        (fderiv ℝ (mollify (hdelta k) U) (r • z)).comp
          (r • ContinuousLinearMap.id ℝ LoopPlane) := by
      simpa only [f, Function.comp_def, id_eq] using hd.fderiv
    rw [hdeq, ContinuousLinearMap.comp_apply, smul_apply,
      ContinuousLinearMap.id_apply, map_smul,
      fderiv_mollify_of_weak_pairing (hdelta k) U (D i) _ (hpair i)]
    rfl
  have hcomp {v w : LoopPlane → ℝ} (hvw : v =ᵐ[volume] w) :
      (fun z => v (r • z)) =ᵐ[volume.restrict loopDiskSet] fun z => w (r • z) :=
    ae_restrict_of_ae ((Measure.quasiMeasurePreserving_smul volume hrpos.ne').ae hvw)
  have hA (k : ℕ) : A k =ᵐ[volume.restrict loopDiskSet] f k :=
    (m65DiskDilationL2_coe r hr _).trans (hcomp (mollifyL2_ae_eq (hdelta k) U))
  have hB (k : ℕ) (i : Fin 2) : B k i =ᵐ[volume.restrict loopDiskSet]
      fun z => fderiv ℝ (f k) z (EuclideanSpace.basisFun (Fin 2) ℝ i) := by
    filter_upwards [Lp.coeFn_smul r (T (mollifyL2 (hdelta k) (D i))),
      (m65DiskDilationL2_coe r hr _).trans
        (hcomp (mollifyL2_ae_eq (hdelta k) (D i)))] with z hs hd
    rw [hs, Pi.smul_apply, hd, hdf]
    rfl
  have hAlim : Tendsto A atTop (𝓝 (T Zu)) := by
    rw [← hTU]
    exact (T.continuous.tendsto U).comp (tendsto_mollifyL2 delta hdelta hdelta0 U)
  have hBlim (i : Fin 2) : Tendsto (fun k => B k i) atTop (𝓝 (r • T (Zd i))) := by
    rw [← hTD i]
    exact tendsto_const_nhds.smul ((T.continuous.tendsto (D i)).comp
      (tendsto_mollifyL2 delta hdelta hdelta0 (D i)))
  have hAe : ∀ᶠ k in atTop, dist (A k) (T Zu) < eps :=
    hAlim.eventually (ball_mem_nhds _ heps)
  have hBe : ∀ᶠ k in atTop, ∀ i, dist (B k i) (r • T (Zd i)) < eps :=
    Filter.eventually_all.mpr (fun i => (hBlim i).eventually (ball_mem_nhds _ heps))
  obtain ⟨k, hkA, hkB⟩ := (hAe.and hBe).exists
  exact ⟨f k, A k, B k, hf k, hA k, hB k, hkA, hkB⟩

theorem m65WeakTrace_exists_smooth_graph
    {u : Lp ℝ 2 (volume.restrict loopDiskSet)}
    {d : Fin 2 → Lp ℝ 2 (volume.restrict loopDiskSet)}
    {b : Lp ℝ 2 (volume.restrict (Icc (-Real.pi) Real.pi))}
    (htrace : M65DiskWeakTrace u d b) :
    ∃ (f : ℕ → LoopPlane → ℝ)
      (A : ℕ → Lp ℝ 2 (volume.restrict loopDiskSet))
      (B : ℕ → Fin 2 → Lp ℝ 2 (volume.restrict loopDiskSet)),
      (∀ n, ContDiff ℝ ∞ (f n)) ∧
      (∀ n, A n =ᵐ[volume.restrict loopDiskSet] f n) ∧
      (∀ n i, B n i =ᵐ[volume.restrict loopDiskSet]
        fun z => fderiv ℝ (f n) z (EuclideanSpace.basisFun (Fin 2) ℝ i)) ∧
      Tendsto A atTop (𝓝 u) ∧ ∀ i, Tendsto (fun n => B n i) atTop (𝓝 (d i)) := by
  classical
  have hs : MeasurableSet loopDiskSet := measurableSet_closedBall
  let extend (w : Lp ℝ 2 (volume.restrict loopDiskSet)) :
      Lp ℝ 2 (volume : Measure LoopPlane) :=
    ((memLp_indicator_iff_restrict hs).mpr (Lp.memLp w)).toLp
      (loopDiskSet.indicator (w : LoopPlane → ℝ))
  have hextend (w : Lp ℝ 2 (volume.restrict loopDiskSet)) :
      extend w =ᵐ[volume] loopDiskSet.indicator (w : LoopPlane → ℝ) := MemLp.coeFn_toLp _
  have hrestrict (w : Lp ℝ 2 (volume.restrict loopDiskSet)) :
      m65DiskDilationL2 1 (by norm_num) (extend w) = w := by
    apply Lp.ext
    simpa only [one_smul] using
      m65Dilation_indicator_coe (by norm_num) le_rfl (extend w) _ (hextend w)
  let r (n : ℕ) : ℝ := 1 - 1 / ((n : ℝ) + 3)
  have hr (n : ℕ) : 1 / 2 ≤ r n := by
    have hi : 1 / ((n : ℝ) + 3) ≤ (1 : ℝ) / 2 := by
      rw [div_le_div_iff₀ (by positivity : 0 < (n : ℝ) + 3) (by norm_num : (0 : ℝ) < 2)]
      linarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]
    dsimp only [r]
    linarith
  have hr1 (n : ℕ) : r n < 1 := by
    dsimp only [r]
    have hp : 0 < 1 / ((n : ℝ) + 3) := by positivity
    linarith
  have hrlim : Tendsto r atTop (𝓝 1) := by
    have hh := (tendsto_add_atTop_iff_nat 3).2
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa only [r, Nat.cast_add, Nat.cast_ofNat, sub_zero] using
      (tendsto_const_nhds (x := (1 : ℝ))).sub hh
  let eps (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have heps (n : ℕ) : 0 < eps n := by dsimp only [eps]; positivity
  have heps0 : Tendsto eps atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose f A B hf hA hB hdistA hdistB using fun n =>
    m65WeakTrace_approximate_at_scale htrace (extend u) (fun i => extend (d i))
      (hextend u) (fun i => hextend (d i)) (hr n) (hr1 n) (heps n)
  refine ⟨f, A, B, hf, hA, hB, ?_, ?_⟩
  · have hlim := m65DiskDilationL2_tendsto r hr hrlim (extend u)
    rw [hrestrict] at hlim
    apply hlim.congr_dist
    apply squeeze_zero (fun _ => dist_nonneg) _ heps0
    intro n
    rw [dist_comm]
    exact (hdistA n).le
  · intro i
    have hlim := hrlim.smul (m65DiskDilationL2_tendsto r hr hrlim (extend (d i)))
    rw [hrestrict, one_smul] at hlim
    apply hlim.congr_dist
    apply squeeze_zero (fun _ => dist_nonneg) _ heps0
    intro n
    rw [dist_comm]
    exact (hdistB n i).le

end PoincareConjecture
