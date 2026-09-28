import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.StrictTraceBoundaryReality
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.HartmanWintner

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Complex Metric
open scoped Topology ContDiff

namespace PoincareConjecture.M65StrictTrace

open M65Branch

theorem halfDisk_differential_zero_alternative
    {g : RiemannianMetric 3 LoopAmbient} (D : LeviCivitaData g)
    {H : ℂ → LoopAmbient} {r : ℝ} (hr : 0 < r)
    {c : ℝ → LoopAmbient} {I J : Set ℝ} {U : Set LoopAmbient}
    {sigma : LoopAmbient → ℝ} {V : LoopAmbient → LoopAmbient} (j : Fin 3)
    (hI : IsOpen I) (hU : IsOpen U) (hc : ContDiffOn ℝ ∞ c I)
    (hsigma : ContDiffOn ℝ ∞ sigma U) (hV : ContDiffOn ℝ ∞ V U)
    (hH : ContDiffOn ℝ 1 H (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}))
    (hHi : ContDiffOn ℝ ∞ H (ball (0 : ℂ) r ∩ {z | 0 < z.im}))
    (hHU : MapsTo H (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}) U)
    (hparam : ∀ q ∈ U, sigma q ∈ I)
    (hinv : ∀ s ∈ J, sigma (c s) = s)
    (hVeq : ∀ q ∈ U, V q = deriv c (sigma q))
    (hj : ∀ q ∈ U, V q j ≠ 0)
    (harc : ∀ s : ℝ, ‖(s : ℂ)‖ ≤ r → H (s : ℂ) ∈ c '' J)
    (hconf : ∀ z ∈ closedBall (0 : ℂ) r ∩ {w | 0 ≤ w.im},
      let T := fderivWithin ℝ H (closedBall (0 : ℂ) r ∩ {w | 0 ≤ w.im}) z
      g.inner (H z) (T 1) (T 1) = g.inner (H z) (T Complex.I) (T Complex.I) ∧
        g.inner (H z) (T 1) (T Complex.I) = 0)
    (heq : ∀ z ∈ ball (0 : ℂ) r ∩ {w | 0 < w.im},
      dbar (complexGradient H) z = harmonicMatrix D H z (complexGradient H z)) :
    (∀ᶠ z in 𝓝[{z : ℂ | 0 ≤ z.im}] 0,
      fderivWithin ℝ H (closedBall (0 : ℂ) r ∩ {w | 0 ≤ w.im}) z = 0) ∨
      ∀ᶠ z in 𝓝[{z : ℂ | 0 ≤ z.im}] 0,
        fderivWithin ℝ H (closedBall (0 : ℂ) r ∩ {w | 0 ≤ w.im}) z = 0 → z = 0 := by
  let K := closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}
  let W := ball (0 : ℂ) r ∩ {z | 0 < z.im}
  let L := fun q => complexifyOperator (rowFrame (g.inner q) (V q) j)
  let F := halfDiskFramedGradient H L r
  let A := halfDiskFramedMatrix D H L r
  have hG : ContDiffOn ℝ ∞ g.euclideanCoefficients U :=
    (contDiff_iff_contDiffAt.mpr g.contDiffAt_euclideanCoefficients).contDiffOn
  have hL : ContDiffOn ℝ ∞ L U := complexifyOperator.contDiff.comp_contDiffOn
    (contDiffOn_rowFrame j hG hV hj)
  have hunit (z : ℂ) (hz : z ∈ K) : IsUnit (L (H z)) :=
    rowFrame_complex_isUnit _ _ j (hj _ (hHU hz)) (g.pos _)
  have hWsub : W ⊆ K := fun z hz =>
    ⟨ball_subset_closedBall hz.1, (show 0 < z.im from hz.2).le⟩
  obtain ⟨hFc, hAc⟩ := halfDiskFramed_fields_continuousOn D hr hU hL hH hHU hunit
  obtain ⟨hFi, hAi, hFeq⟩ := halfDiskFramed_fields_equation D hU hL hHi
    (hHU.mono hWsub Subset.rfl) (fun z hz => hunit z (hWsub hz)) heq
  have hzero (z : ℂ) (hz : z ∈ K) : F z = 0 ↔ fderivWithin ℝ H K z = 0 := by
    rw [← halfDiskGradient_eq_zero_iff H r z]
    constructor
    · intro h
      have hh := congrArg (fun v => Ring.inverse (L (H z)) v) h
      change (Ring.inverse (L (H z)) * L (H z)) (halfDiskGradient H r z) = _ at hh
      rw [Ring.inverse_mul_cancel _ (hunit z hz)] at hh
      simpa using hh
    · intro h
      change L (H z) (halfDiskGradient H r z) = 0
      rw [h, map_zero]
  have hr2 : 0 < r / 2 := half_pos hr
  have hK2 : closedBall (0 : ℂ) (r / 2) ∩ {z | 0 ≤ z.im} ⊆ K := by
    intro z hz
    exact ⟨closedBall_subset_closedBall (by linarith) hz.1, hz.2⟩
  have hW2 : ball (0 : ℂ) (r / 2) ∩ {z | 0 < z.im} ⊆ W := by
    intro z hz
    exact ⟨ball_subset_ball (by linarith) hz.1, hz.2⟩
  have hreal (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) (r / 2)) (hi : z.im = 0) :
      boundaryReflection j (F z) = F z := by
    have hzlt : ‖z‖ < r := (mem_closedBall_zero_iff.mp hz).trans_lt (by linarith)
    have he : (z.re : ℂ) = z := by apply Complex.ext <;> simp [hi]
    have hm : z ∈ K := ⟨mem_closedBall_zero_iff.mpr hzlt.le, by simp [hi]⟩
    have hmr : (z.re : ℂ) ∈ K := he.symm ▸ hm
    have hh := halfDisk_rowFrame_reality j hI hU hc hsigma hH hHU hparam hinv hVeq hj harc
      (by simpa only [he] using hzlt)
      (hconf (z.re : ℂ) hmr).1 (hconf (z.re : ℂ) hmr).2
    exact Eq.mp (congrArg (fun w => boundaryReflection j (F w) = F w) he) hh
  obtain ⟨A0, R, B, _, _, _, _, _, _, _, _, _, hcases⟩ :=
    exists_half_disk_power_factor (boundaryReflection j) (boundaryReflection_smul j)
      (boundaryReflection_involutive j) hr2 (hFc.mono hK2) (hFi.mono hW2)
      (hAc.mono hK2) (hAi.mono hW2)
      (fun z hz hi => hFeq z (hW2 ⟨hz, hi⟩)) hreal
  have hnearK : ∀ᶠ z in 𝓝[{z : ℂ | 0 ≤ z.im}] 0, z ∈ K := by
    have hball : ∀ᶠ z : ℂ in 𝓝 0, z ∈ ball (0 : ℂ) r :=
      isOpen_ball.mem_nhds (mem_ball_self hr)
    filter_upwards [hball.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with z hz hi
    exact ⟨ball_subset_closedBall hz, hi⟩
  rcases hcases with hlocal | ⟨m, Q, _, _, hQ0, hQc, hfactor⟩
  · left
    filter_upwards [hlocal, hnearK] with z hz hzK
    exact (hzero z hzK).mp hz
  · right
    filter_upwards [hfactor, hnearK,
      (hQc.eventually_ne hQ0).filter_mono nhdsWithin_le_nhds] with z hzf hzK hzQ hz
    by_contra hne
    have hp : z ^ m ≠ 0 := pow_ne_zero m hne
    exact (smul_ne_zero hp hzQ) (hzf.symm.trans ((hzero z hzK).mpr hz))

end PoincareConjecture.M65StrictTrace
