import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryWeakSeamFlux











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Function
open scoped ContDiff Topology

namespace PoincareConjecture

local notation "P" => curvePeriod
local notation "aP" => annulusPoint curvePeriod 0
local notation "e0" => EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
local notation "e1" => EuclideanSpace.single (1 : Fin 2) (1 : ℝ)



def m64BoundarySeamCutoff (R : ℝ) (N : ℕ) (p : LoopPlane) : ℝ :=
  m64BoundaryAveragedCutoff 0 R N p + m64BoundaryAveragedCutoff aP R N p



theorem m64BoundarySeamCutoff_contDiff (R : ℝ) (N : ℕ) :
    ContDiff ℝ ∞ (m64BoundarySeamCutoff R N) :=
  (m64BoundaryAveragedCutoff_contDiff 0 R N).add
    (m64BoundaryAveragedCutoff_contDiff aP R N)

private theorem cutoff_norm_horizontal (t x : ℝ) :
    ‖annulusPoint t 0 - annulusPoint x 0‖ = |t - x| := by
  have heq : annulusPoint t 0 - annulusPoint x 0 =
      EuclideanSpace.single (0 : Fin 2) (t - x) := by
    ext i
    fin_cases i <;> simp [annulusPoint]
  rw [heq]
  simpa only [Real.norm_eq_abs] using PiLp.norm_single 2 (fun _ : Fin 2 => ℝ) 0 (t - x)

private theorem annulusPoint_zero_zero : annulusPoint 0 0 = (0 : LoopPlane) := by
  ext i
  fin_cases i <;> simp [annulusPoint]

private theorem averaged_zero_of_coordinate {a p : LoopPlane} {R : ℝ}
    (hR : 0 < R) (N : ℕ) (i : Fin 2) (hp : R ≤ |p i - a i|) :
    m64BoundaryAveragedCutoff a R N p = 0 := by
  apply m64BoundaryAveragedCutoff_eq_zero hR N
  exact hp.trans (by simpa only [PiLp.sub_apply, Real.norm_eq_abs] using
    PiLp.norm_apply_le (p - a) i)



theorem m64BoundarySeamCutoff_nonneg (R : ℝ) (N : ℕ) (p : LoopPlane) :
    0 ≤ m64BoundarySeamCutoff R N p := add_nonneg
  (m64BoundaryAveragedCutoff_nonneg 0 R N p) (m64BoundaryAveragedCutoff_nonneg aP R N p)



theorem m64BoundarySeamCutoff_le_one {R : ℝ} (hR : 0 < R) (hRP : 2 * R < P)
    {N : ℕ} (hN : 0 < N) (p : LoopPlane) : m64BoundarySeamCutoff R N p ≤ 1 := by
  have hP : 0 < P := by unfold curvePeriod; positivity
  have hnorm : ‖aP‖ = P := by
    simpa only [annulusPoint_zero_zero, sub_zero, sub_zero, abs_of_pos hP] using
      cutoff_norm_horizontal P 0
  have hd : R ≤ ‖p - 0‖ ∨ R ≤ ‖p - aP‖ := by
    by_contra h
    push Not at h
    have hh : ‖aP‖ ≤ ‖p - 0‖ + ‖p - aP‖ := by
      simpa only [add_sub_cancel, sub_zero, norm_sub_rev] using norm_add_le p (aP - p)
    linarith
  rcases hd with hd | hd
  · simp only [m64BoundarySeamCutoff, m64BoundaryAveragedCutoff_eq_zero hR N hd, zero_add]
    exact m64BoundaryAveragedCutoff_le_one aP R hN p
  · simp only [m64BoundarySeamCutoff, m64BoundaryAveragedCutoff_eq_zero hR N hd, add_zero]
    exact m64BoundaryAveragedCutoff_le_one 0 R hN p



theorem m64BoundarySeamCutoff_bottom_profile {R : ℝ} (hR : 0 < R) (hRP : 2 * R < P)
    {N : ℕ} (hN : 0 < N) :
    let q := fun t => m64BoundarySeamCutoff R N (annulusPoint t 0)
    let d := m64BoundaryCutoffRadius R N / 2
    q 0 = 1 ∧ q P = 1 ∧ q (P / 2) = 0 ∧
      (∀ t ∈ Icc (0 : ℝ) d, q t = 1) ∧
      (∀ t ∈ Icc (P - d) P, q t = 1) ∧
      AntitoneOn q (Icc (0 : ℝ) (P / 2)) ∧ MonotoneOn q (Icc (P / 2) P) := by
  let U := m64BoundaryAveragedCutoff 0 R N
  let W := m64BoundaryAveragedCutoff aP R N
  have hRle : m64BoundaryCutoffRadius R N ≤ R := by
    simpa only [m64BoundaryCutoffRadius, pow_zero, div_one] using
      m64BoundaryCutoffRadius_antitone hR (Nat.zero_le N)
  have hzeroW (t : ℝ) (ht : t ≤ P / 2) : W (annulusPoint t 0) = 0 := by
    apply averaged_zero_of_coordinate hR N 0
    simp only [annulusPoint, Matrix.cons_val_zero]
    rw [abs_of_nonpos (by linarith : t - P ≤ 0)]
    linarith
  have hzeroU (t : ℝ) (ht : P / 2 ≤ t) : U (annulusPoint t 0) = 0 := by
    apply averaged_zero_of_coordinate hR N 0
    simp only [annulusPoint, Matrix.cons_val_zero, PiLp.zero_apply, sub_zero]
    rw [abs_of_nonneg (by linarith : 0 ≤ t)]
    linarith
  have hflat0 (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (m64BoundaryCutoffRadius R N / 2)) :
      m64BoundarySeamCutoff R N (annulusPoint t 0) = 1 := by
    have hU : U (annulusPoint t 0) = 1 := by
      apply m64BoundaryAveragedCutoff_eq_one hR hN
      rw [← annulusPoint_zero_zero, cutoff_norm_horizontal, sub_zero, abs_of_nonneg ht.1]
      exact ht.2
    change U _ + W _ = 1
    rw [hU, hzeroW t (by linarith [ht.2])]
    norm_num
  have hflatP (t : ℝ) (ht : t ∈ Icc (P - m64BoundaryCutoffRadius R N / 2) P) :
      m64BoundarySeamCutoff R N (annulusPoint t 0) = 1 := by
    have hW : W (annulusPoint t 0) = 1 := by
      apply m64BoundaryAveragedCutoff_eq_one hR hN
      rw [cutoff_norm_horizontal, abs_of_nonpos (sub_nonpos.mpr ht.2)]
      linarith [ht.1]
    change U _ + W _ = 1
    rw [hW, hzeroU t (by linarith [ht.1])]
    norm_num
  refine ⟨hflat0 0 ⟨le_rfl, (half_pos (m64BoundaryCutoffRadius_pos hR N)).le⟩,
    hflatP P ⟨by linarith [m64BoundaryCutoffRadius_pos hR N], le_rfl⟩,
    ?_, hflat0, hflatP, ?_, ?_⟩
  · change U _ + W _ = 0
    rw [hzeroU _ le_rfl, hzeroW _ le_rfl, add_zero]
  · intro s hs t ht hst
    change U _ + W _ ≤ U _ + W _
    rw [hzeroW s hs.2, hzeroW t ht.2, add_zero, add_zero]
    apply m64BoundaryAveragedCutoff_antitone_radius hR N
    rw [← annulusPoint_zero_zero, cutoff_norm_horizontal, cutoff_norm_horizontal,
      sub_zero, sub_zero, abs_of_nonneg hs.1, abs_of_nonneg ht.1]
    exact hst
  · intro s hs t ht hst
    change U _ + W _ ≤ U _ + W _
    rw [hzeroU s hs.1, hzeroU t ht.1, zero_add, zero_add]
    apply m64BoundaryAveragedCutoff_antitone_radius hR N
    rw [cutoff_norm_horizontal, cutoff_norm_horizontal,
      abs_of_nonpos (sub_nonpos.mpr ht.2), abs_of_nonpos (sub_nonpos.mpr hs.2)]
    linarith



theorem m64BoundarySeamCutoff_top_zero {R : ℝ} (hR : 0 < R) (hR1 : R < 1)
    (N : ℕ) (t : ℝ) : m64BoundarySeamCutoff R N (annulusPoint t 1) = 0 := by
  have h0 := averaged_zero_of_coordinate (a := (0 : LoopPlane)) (p := annulusPoint t 1)
    hR N 1 (by simpa [annulusPoint] using hR1.le)
  have h1 := averaged_zero_of_coordinate (a := aP) (p := annulusPoint t 1)
    hR N 1 (by simpa [annulusPoint] using hR1.le)
  simp only [m64BoundarySeamCutoff, h0, h1, add_zero]



theorem m64BoundarySeamCutoff_top_fderiv {R : ℝ} (hR : 0 < R) (hR1 : R < 1)
    (N : ℕ) (t : ℝ) : fderiv ℝ (m64BoundarySeamCutoff R N) (annulusPoint t 1) = 0 := by
  apply IsLocalMin.fderiv_eq_zero
  exact Filter.Eventually.of_forall (fun p => by
    rw [m64BoundarySeamCutoff_top_zero hR hR1]
    exact m64BoundarySeamCutoff_nonneg R N p)



theorem m64BoundarySeamCutoff_periodic_derivative {R : ℝ} (hR : 0 < R) (hRP : R < P)
    (N : ℕ) (s : ℝ) :
    fderiv ℝ (m64BoundarySeamCutoff R N) (annulusPoint P s) e1 =
      fderiv ℝ (m64BoundarySeamCutoff R N) (annulusPoint 0 s) e1 := by
  have heq : (fun t => m64BoundarySeamCutoff R N (annulusPoint P t)) =
      (fun t => m64BoundarySeamCutoff R N (annulusPoint 0 t)) := by
    funext t
    have h0 := averaged_zero_of_coordinate (a := (0 : LoopPlane)) (p := annulusPoint P t)
      hR N 0 (by simpa [annulusPoint, abs_of_pos (hR.trans hRP)] using hRP.le)
    have h1 := averaged_zero_of_coordinate (a := aP) (p := annulusPoint 0 t)
      hR N 0 (by simpa [annulusPoint, abs_of_pos (hR.trans hRP)] using hRP.le)
    simp only [m64BoundarySeamCutoff, h0, h1, zero_add, add_zero]
    have he : annulusPoint P t - aP = annulusPoint 0 t := by
      ext i
      fin_cases i <;> simp [annulusPoint]
    simp only [m64BoundaryAveragedCutoff, m64BoundaryRadialCutoff, he, sub_zero]
  have hd (x t : ℝ) : HasDerivAt (fun t => m64BoundarySeamCutoff R N (annulusPoint x t))
      (fderiv ℝ (m64BoundarySeamCutoff R N) (annulusPoint x t) e1) t := by
    have hp : (fun t : ℝ => annulusPoint x t) = (fun t : ℝ => x • e0 + t • e1) := by
      ext t i
      fin_cases i <;> simp [annulusPoint]
    have hpd : HasDerivAt (fun t : ℝ => annulusPoint x t) e1 t := by
      rw [hp]
      simpa using ((hasDerivAt_id t).smul_const e1).const_add (x • e0)
    exact ((m64BoundarySeamCutoff_contDiff R N).differentiable
      (by simp) _).hasFDerivAt.comp_hasDerivAt t hpd
  exact (hd P s).deriv.symm.trans ((congrArg (fun f : ℝ → ℝ => deriv f s) heq).trans (hd 0 s).deriv)



theorem m64BoundarySeamCutoff_column_energy_le {R : ℝ} (hR : 0 < R)
    {N : ℕ} (hN : 0 < N) (i : Fin 2) :
    (∫ p in interior m64AnnulusDomain, (fderiv ℝ (m64BoundarySeamCutoff R N) p
      (EuclideanSpace.single i 1)) ^ 2) ≤
      4 * (∫ p, (fderiv ℝ (m64BoundaryRadialCutoff 0 1) p
        (EuclideanSpace.single i 1)) ^ 2) / N := by
  let U := m64BoundaryAveragedCutoff 0 R N
  let W := m64BoundaryAveragedCutoff aP R N
  let dU := fun p => fderiv ℝ U p (EuclideanSpace.single i 1)
  let dW := fun p => fderiv ℝ W p (EuclideanSpace.single i 1)
  have hi (a : LoopPlane) : Integrable (fun p =>
      (fderiv ℝ (m64BoundaryAveragedCutoff a R N) p (EuclideanSpace.single i 1)) ^ 2) := by
    have hc : Continuous (fun p => fderiv ℝ (m64BoundaryAveragedCutoff a R N) p
        (EuclideanSpace.single i 1)) :=
      ((m64BoundaryAveragedCutoff_contDiff a R N).continuous_fderiv
        (by simp)).clm_apply continuous_const
    have hs : HasCompactSupport (m64BoundaryAveragedCutoff a R N) := by
      apply HasCompactSupport.intro (isCompact_closedBall a R)
      intro p hp
      apply m64BoundaryAveragedCutoff_eq_zero hR N
      exact le_of_lt (by simpa only [Metric.mem_closedBall, dist_eq_norm, not_le] using hp)
    apply (hc.pow 2).integrable_of_hasCompactSupport
    simpa only [pow_two] using (hs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)).mul_right
      (f' := fun p => fderiv ℝ (m64BoundaryAveragedCutoff a R N) p (EuclideanSpace.single i 1))
  have hd (p : LoopPlane) : fderiv ℝ (m64BoundarySeamCutoff R N) p (EuclideanSpace.single i 1) =
      dU p + dW p := by
    rw [show m64BoundarySeamCutoff R N = U + W from rfl,
      fderiv_add ((m64BoundaryAveragedCutoff_contDiff 0 R N).differentiable (by simp) p)
        ((m64BoundaryAveragedCutoff_contDiff aP R N).differentiable (by simp) p)]
    rfl
  have hpair : Integrable (fun p => (dU p + dW p) ^ 2) :=
    ((memLp_two_iff_integrable_sq
      (((m64BoundaryAveragedCutoff_contDiff 0 R N).continuous_fderiv (by simp)).clm_apply
        continuous_const).aestronglyMeasurable).mpr (hi 0) |>.add
      ((memLp_two_iff_integrable_sq
      (((m64BoundaryAveragedCutoff_contDiff aP R N).continuous_fderiv (by simp)).clm_apply
        continuous_const).aestronglyMeasurable).mpr (hi aP))).integrable_sq
  simp_rw [hd]
  calc
    _ ≤ ∫ p, (dU p + dW p) ^ 2 :=
      setIntegral_le_integral hpair (Eventually.of_forall (fun _ => sq_nonneg _))
    _ ≤ ∫ p, 2 * (dU p ^ 2 + dW p ^ 2) := by
      apply integral_mono hpair (((hi 0).add (hi aP)).const_mul 2)
      intro p
      change (dU p + dW p) ^ 2 ≤ 2 * (dU p ^ 2 + dW p ^ 2)
      nlinarith [sq_nonneg (dU p - dW p)]
    _ = _ := by
      rw [integral_const_mul, integral_add (hi 0) (hi aP)]
      rw [m64BoundaryAveragedCutoff_column_energy 0 hR hN i,
        m64BoundaryAveragedCutoff_column_energy aP hR hN i]
      ring

end PoincareConjecture
