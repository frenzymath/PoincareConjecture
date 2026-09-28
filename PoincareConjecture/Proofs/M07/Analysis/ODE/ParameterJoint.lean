import PoincareConjecture.Proofs.M07.Analysis.ODE.ParameterSmooth
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section

open Set Filter Function Metric
open scoped Topology ContDiff NNReal

set_option linter.unusedSectionVars false

namespace Poincare.ODE.Parameter

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] [FiniteDimensional ℝ F]

set_option maxHeartbeats 1600000 in

theorem exists_local_flow_joint_contDiff (f : F → F) (hf : ContDiff ℝ ∞ f) (z₀ : F) :
    ∃ (r δ : ℝ) (Φ : F → ℝ → F), 0 < r ∧ 0 < δ ∧
      (∀ z ∈ ball z₀ r,
        Φ z 0 = z ∧
        (∀ t ∈ Ioo (-δ) δ, HasDerivAt (Φ z) (f (Φ z t)) t)) ∧
      ContDiffOn ℝ ∞ (fun p : F × ℝ => Φ p.1 p.2)
        (ball z₀ r ×ˢ Ioo (-δ) δ) := by
  classical
  let fhat : (F × ℝ) → (F × ℝ) := fun za => (za.2 • f za.1, 0)
  have hfhat : ContDiff ℝ ∞ fhat := by
    exact (contDiff_snd.smul (hf.comp contDiff_fst)).prodMk contDiff_const
  obtain ⟨r₀, ε₀, T₀, Z₀, L₀, σ₀, hT₀, hr₀, hε₀, hTε₀, hflow₀, hLip₀,
      hσ₀, hσC₀⟩ := exists_local_flow_contDiffAt f hf z₀
  obtain ⟨rhat, epshat, That, Zhat, Lhat, sigmahat, hThat, hrhat, hepshat, hTepshat, hflowhat, hLiphat,
      hsigmahat, hsigmaChat⟩ := exists_local_flow_contDiffAt fhat hfhat (z₀, (0 : ℝ))
  have hdfhat : Continuous (fderiv ℝ fhat) := hfhat.continuous_fderiv (by simp)
  obtain ⟨C, hC⟩ := (isCompact_closedBall ((z₀, (0 : ℝ)) : F × ℝ) 1).exists_bound_of_continuousOn
    hdfhat.continuousOn
  have hC0 : 0 ≤ C := le_trans (norm_nonneg (fderiv ℝ fhat (z₀, 0)))
    (hC (z₀, 0) (mem_closedBall_self zero_le_one))
  let K : ℝ≥0 := ⟨C, hC0⟩
  have hLiphatBall : LipschitzOnWith K fhat
      (closedBall ((z₀, (0 : ℝ)) : F × ℝ) 1) := by
    apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
    · intro x hx
      exact (hfhat.differentiable (by simp)).differentiableAt
    · intro x hx
      exact_mod_cast hC x hx
    · exact convex_closedBall _ _
  let r : ℝ := min r₀ rhat / 2
  let lam : ℝ := min 1 (min rhat (ε₀ / That)) / 2
  let δ : ℝ := That * lam
  have hrpos : 0 < r := by
    dsimp [r]
    positivity
  have hLamPos : 0 < lam := by
    dsimp [lam]
    have hεdiv : 0 < ε₀ / That := div_pos hε₀ hThat
    positivity
  have hδpos : 0 < δ := by
    dsimp [δ]
    positivity
  have hr_r₀ : r < r₀ := by
    dsimp [r]
    have : 0 < min r₀ rhat := lt_min hr₀ hrhat
    linarith [min_le_left r₀ rhat]
  have hr_rhat : r < rhat := by
    dsimp [r]
    have : 0 < min r₀ rhat := lt_min hr₀ hrhat
    linarith [min_le_right r₀ rhat]
  have hLamOne : lam < 1 := by
    dsimp [lam]
    have : min 1 (min rhat (ε₀ / That)) ≤ 1 := min_le_left _ _
    linarith
  have hLamRhat : lam < rhat := by
    dsimp [lam]
    have : min 1 (min rhat (ε₀ / That)) ≤ rhat :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  have hLamTime : That * lam < ε₀ := by
    dsimp [lam]
    have hdiv : min 1 (min rhat (ε₀ / That)) ≤ ε₀ / That :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    have hmul : That * (min 1 (min rhat (ε₀ / That))) ≤ ε₀ := by
      rw [le_div_iff₀ hThat] at hdiv
      simpa [mul_comm] using hdiv
    linarith
  have hThatmem : (That : ℝ) ∈ Icc (0 : ℝ) That := ⟨hThat.le, le_rfl⟩
  let tT : Set.Icc (0 : ℝ) That := ⟨That, hThatmem⟩
  have hP : ContDiffOn ℝ ∞
      (fun za : F × ℝ => (sigmahat za tT).1)
      (ball ((z₀, (0 : ℝ)) : F × ℝ) rhat) := by
    intro za hza
    have hev : ContDiffAt ℝ ∞ sigmahat za := hsigmaChat za hza
    have heval : ContDiff ℝ ∞
        (fun w : C(Set.Icc (0 : ℝ) That, F × ℝ) => (w tT).1) := by
      exact (ContinuousLinearMap.fst ℝ F ℝ).comp
        (ContinuousMap.evalCLM ℝ tT) |>.contDiff
    exact (heval.contDiffAt.comp za hev).contDiffWithinAt
  let Φ : F → ℝ → F := fun z t =>
    (sigmahat (z, t / That) tT).1
  have hpair_mem : ∀ z ∈ ball z₀ r, ∀ t ∈ Ioo (-δ) δ,
      (z, t / That) ∈ ball ((z₀, (0 : ℝ)) : F × ℝ) rhat := by
    intro z hz t ht
    have hz' : dist z z₀ < rhat := lt_of_lt_of_le
      (mem_ball.mp hz) (le_of_lt hr_rhat)
    have ht' : |t| < δ := abs_lt.mpr ht
    have ha : |t / That| < lam := by
      rw [abs_div, abs_of_pos hThat, div_lt_iff₀ hThat]
      simpa [δ, mul_comm] using ht'
    rw [mem_ball, Prod.dist_eq]
    refine max_lt hz' ?_
    simpa [Real.dist_eq, abs_div, abs_of_pos hThat] using
      (lt_trans ha hLamRhat)
  have hΦsmooth : ContDiffOn ℝ ∞
      (fun p : F × ℝ => Φ p.1 p.2)
      (ball z₀ r ×ˢ Ioo (-δ) δ) := by
    have harg : ContDiff ℝ ∞
        (fun p : F × ℝ => (p.1, p.2 / That)) := by
      exact contDiff_fst.prodMk (contDiff_snd.div_const That)
    have hmaps : MapsTo (fun p : F × ℝ => (p.1, p.2 / That))
        (ball z₀ r ×ˢ Ioo (-δ) δ)
        (ball ((z₀, (0 : ℝ)) : F × ℝ) rhat) := by
      intro p hp
      exact hpair_mem p.1 hp.1 p.2 hp.2
    have hc := hP.comp harg.contDiffOn hmaps
    exact hc.congr fun p hp => rfl
  have hΦeq : ∀ z ∈ ball z₀ r, ∀ t ∈ Ioo (-δ) δ,
      Φ z t = Z₀ z t := by
    intro z hz t ht
    let a : ℝ := t / That
    have ha : |a| < lam := by
      dsimp [a]
      exact (by
        rw [abs_div, abs_of_pos hThat, div_lt_iff₀ hThat]
        simpa [δ, mul_comm] using (abs_lt.mpr ht))
    have ha1 : |a| < 1 := lt_of_lt_of_le ha (le_of_lt hLamOne)
    have hat : |a| * That < ε₀ := by
      calc
        |a| * That = |t| := by
          dsimp [a]
          rw [abs_div, abs_of_pos hThat]
          field_simp
        _ < δ := abs_lt.mpr ht
        _ < ε₀ := hLamTime
    have hz₀c : z ∈ closedBall z₀ r₀ := by
      apply mem_closedBall.mpr
      exact le_trans (le_of_lt (mem_ball.mp hz)) (le_of_lt hr_r₀)
    have hza : (z, a) ∈ closedBall ((z₀, (0 : ℝ)) : F × ℝ) rhat :=
      ball_subset_closedBall (hpair_mem z hz t ht)
    let u : ℝ → F × ℝ := fun s => (Z₀ z (a * s), a)
    let v : ℝ → F × ℝ := fun s => Zhat (z, a) s
    have hu_mem : ∀ s ∈ Icc (-That) That,
        (Z₀ z (a * s), a) ∈ closedBall ((z₀, (0 : ℝ)) : F × ℝ) 1 := by
      intro s hs
      have hst : |a * s| < ε₀ := by
        rw [abs_mul]
        have hs' : |s| ≤ That := by
          exact abs_le.mpr ⟨by linarith [hs.1], hs.2⟩
        exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hs' (abs_nonneg a)) hat
      have hst' := abs_lt.mp hst
      have hmem0 : a * s ∈ Icc (-ε₀) ε₀ :=
        ⟨le_of_lt hst'.1, le_of_lt hst'.2⟩
      rw [mem_closedBall, Prod.dist_eq]
      refine max_le ?_ ?_
      · exact le_of_lt ((hflow₀ z hz₀c).2.2 (a * s) hmem0)
      · simpa [Real.dist_eq] using le_of_lt ha1
    have hv_mem : ∀ s ∈ Icc (-That) That,
        v s ∈ closedBall ((z₀, (0 : ℝ)) : F × ℝ) 1 := by
      intro s hs
      have hs' : -That ≤ s ∧ s ≤ That := hs
      have hneg : -epshat ≤ s := by linarith [hs'.1, hTepshat]
      have hpos : s ≤ epshat := by linarith [hs'.2, hTepshat]
      exact ball_subset_closedBall ((hflowhat _ hza).2.2 s ⟨hneg, hpos⟩)
    have hu_cont : ContinuousOn u (Icc (-That) That) := by
      have hzc : ContinuousOn (Z₀ z) (Icc (-ε₀) ε₀) := fun s hs =>
        ((hflow₀ z hz₀c).2.1 s hs).continuousWithinAt
      have hlin : Continuous (fun s : ℝ => a * s) := continuous_const.mul continuous_id
      have hmap : MapsTo (fun s : ℝ => a * s) (Icc (-That) That) (Icc (-ε₀) ε₀) := by
        intro s hs
        have hst : |a * s| < ε₀ := by
          rw [abs_mul]
          have hs' : |s| ≤ That := abs_le.mpr ⟨by linarith [hs.1], hs.2⟩
          exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hs' (abs_nonneg a)) hat
        have hst' := abs_lt.mp hst
        exact ⟨le_of_lt hst'.1, le_of_lt hst'.2⟩
      exact (hzc.comp hlin.continuousOn hmap).prodMk continuousOn_const
    have hv_cont : ContinuousOn v (Icc (-That) That) := by
      have hcontbig : ContinuousOn (Zhat (z, a)) (Icc (-epshat) epshat) := fun s hs =>
        ((hflowhat _ hza).2.1 s hs).continuousWithinAt
      apply hcontbig.mono
      intro s hs
      have hs' : -That ≤ s ∧ s ≤ That := hs
      have hneg : -epshat ≤ s := by linarith [hs'.1, hTepshat]
      have hpos : s ≤ epshat := by linarith [hs'.2, hTepshat]
      exact ⟨hneg, hpos⟩
    have hF_lip : ∀ s ∈ Ioo (-That) That,
        LipschitzOnWith K (fun y : F × ℝ => fhat y) (closedBall ((z₀, (0 : ℝ)) : F × ℝ) 1) :=
      fun _ _ => hLiphatBall
    have hu_deriv : ∀ s ∈ Ioo (-That) That,
        HasDerivAt u (fhat (u s)) s := by
      intro s hs
      have hst : a * s ∈ Ioo (-ε₀) ε₀ := by
        have hst' : |a * s| < ε₀ := by
          rw [abs_mul]
          have hs' : |s| < That := abs_lt.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
          have hprod : |a| * |s| ≤ |a| * That :=
            mul_le_mul_of_nonneg_left (le_of_lt hs') (abs_nonneg a)
          exact lt_of_le_of_lt hprod hat
        exact abs_lt.mp hst'
      have hbase := ((hflow₀ z hz₀c).2.1 (a * s)
        ⟨hst.1.le, hst.2.le⟩).hasDerivAt (Icc_mem_nhds hst.1 hst.2)
      have hlin := (hasDerivAt_id s).const_mul a
      have hcomp := hbase.scomp s hlin
      have hpair := hcomp.prodMk (hasDerivAt_const s a)
      simpa [u, fhat, mul_comm, smul_eq_mul] using hpair
    have hv_deriv : ∀ s ∈ Ioo (-That) That,
        HasDerivAt v (fhat (v s)) s := by
      intro s hs
      have hsI : s ∈ Ioo (-epshat) epshat := by
        have hs' : -That < s ∧ s < That := hs
        constructor <;> linarith [hTepshat, hs'.1, hs'.2]
      exact ((hflowhat _ hza).2.1 s (Ioo_subset_Icc_self hsI)).hasDerivAt
        (Icc_mem_nhds hsI.1 hsI.2)
    have huv : Set.EqOn u v (Icc (-That) That) := by
      have ht0 : (0 : ℝ) ∈ Ioo (-That) That := ⟨by linarith, hThat⟩
      apply ODE_solution_unique_of_mem_Icc (v := fun _ => fhat)
        (s := fun _ => closedBall ((z₀, (0 : ℝ)) : F × ℝ) 1)
        (K := K) hF_lip ht0 hu_cont hu_deriv
        (fun s hs => hu_mem s ⟨hs.1.le, hs.2.le⟩)
        hv_cont hv_deriv (fun s hs => hv_mem s ⟨hs.1.le, hs.2.le⟩)
      · simp [u, v, hflow₀ z hz₀c |>.1, hflowhat _ hza |>.1]
    have hThatIcc : That ∈ Icc (-That) That := ⟨by linarith [hThat], le_rfl⟩
    have hend := congrArg (fun q : F × ℝ => q.1) (huv hThatIcc)
    have hΦZh : Φ z t = (Zhat (z, a) That).1 := by
      dsimp [Φ]
      rw [hsigmahat (z, a) hza tT]
    rw [hΦZh]
    have harg : a * That = t := by
      dsimp [a]
      field_simp
    simpa [u, v, harg] using hend.symm
  refine ⟨r, δ, Φ, hrpos, hδpos, ?_, hΦsmooth⟩
  intro z hz
  refine ⟨?_, ?_⟩
  · rw [hΦeq z hz 0 ⟨by linarith [hδpos], by linarith [hδpos]⟩]
    exact (hflow₀ z (mem_closedBall.mpr (le_trans (le_of_lt (mem_ball.mp hz))
      (le_of_lt hr_r₀)))).1
  · intro t ht
    have heq : Φ z =ᶠ[𝓝 t] Z₀ z := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      exact hΦeq z hz s hs
    have hder := ((hflow₀ z (mem_closedBall.mpr (le_trans
      (le_of_lt (mem_ball.mp hz)) (le_of_lt hr_r₀)))).2.1 t
        (Ioo_subset_Icc_self (by
          have : |t| < ε₀ := lt_of_lt_of_le (abs_lt.mpr ht) (le_of_lt hLamTime)
          exact abs_lt.mp this))).hasDerivAt
      (Icc_mem_nhds (by
        have : |t| < ε₀ := lt_of_lt_of_le (abs_lt.mpr ht) (le_of_lt hLamTime)
        exact (abs_lt.mp this).1) (by
        have : |t| < ε₀ := lt_of_lt_of_le (abs_lt.mpr ht) (le_of_lt hLamTime)
        exact (abs_lt.mp this).2))
    simpa [hΦeq z hz t ht] using hder.congr_of_eventuallyEq heq

end Poincare.ODE.Parameter
