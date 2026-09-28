import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryMonotoneFlux

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Function
open scoped ContDiff Topology

namespace PoincareConjecture

local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S
local notation "e0" => EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
local notation "e1" => EuclideanSpace.single (1 : Fin 2) (1 : ℝ)

private theorem norm_annulusPoint_sub_lower (t x : ℝ) :
    ‖annulusPoint t 0 - annulusPoint x 0‖ = |t - x| := by
  have heq : annulusPoint t 0 - annulusPoint x 0 =
      EuclideanSpace.single (0 : Fin 2) (t - x) := by
    ext i
    fin_cases i <;> simp [annulusPoint]
  rw [heq]
  simpa only [Real.norm_eq_abs] using PiLp.norm_single 2 (fun _ : Fin 2 => ℝ) 0 (t - x)

theorem m64WeakPhase_monotone_gap_sq_le
    (u : LoopPlane → ℝ) (V : Fin 2 → LoopPlane → ℝ) (b : ℝ → ℝ)
    (hV : ∀ i, MemLp (V i) 2 mu) (hb : Monotone b)
    (hgreen0 : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∀ s : ℝ, phi (annulusPoint 0 s) = 0) →
      (∀ s : ℝ, phi (annulusPoint curvePeriod s) = 0) →
      (∫ p in S, phi p * V 0 p) + (∫ p in S, fderiv ℝ phi p e0 * u p) = 0)
    (hgreen1 : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∀ x : ℝ, phi (annulusPoint x 1) = 0) →
      (∫ p in S, phi p * V 1 p) + (∫ p in S, fderiv ℝ phi p e1 * u p) =
        -(∫ x in Icc (0 : ℝ) curvePeriod, phi (annulusPoint x 0) * b x))
    {x R : ℝ} (hR : 0 < R) (hx : R < x) (hP : x + R < curvePeriod) (hR1 : R < 1)
    {N : ℕ} (hN : 0 < N) :
    (b (x + m64BoundaryCutoffRadius R N / 2) -
      b (x - m64BoundaryCutoffRadius R N / 2)) ^ 2 ≤
      (2 * ((∫ p, (fderiv ℝ (m64BoundaryRadialCutoff 0 1) p e0) ^ 2) +
        ∫ p, (fderiv ℝ (m64BoundaryRadialCutoff 0 1) p e1) ^ 2) *
        ((∫ p in S, (V 0 p) ^ 2) + ∫ p in S, (V 1 p) ^ 2)) / N := by
  let a := annulusPoint x 0
  let eta := m64BoundaryAveragedCutoff a R N
  let q : ℝ → ℝ := fun t => eta (annulusPoint t 0)
  have heta : ContDiff ℝ ∞ eta := m64BoundaryAveragedCutoff_contDiff a R N
  have hpoint : (fun t : ℝ => annulusPoint t 0) = (fun t : ℝ => t • e0) := by
    ext t i
    fin_cases i <;> simp [annulusPoint]
  have hq : ContDiff ℝ 1 q := (heta.of_le (by norm_cast : (1 : ℕ∞ω) ≤ ∞)).comp
    (by rw [hpoint]; exact contDiff_id.smul contDiff_const)
  have hpointd (t : ℝ) : HasDerivAt (fun t : ℝ => annulusPoint t 0) e0 t := by
    rw [hpoint]
    simpa using (hasDerivAt_id t).smul_const e0
  have hqder (t : ℝ) : deriv q t = fderiv ℝ eta (annulusPoint t 0) e0 :=
    ((heta.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t
      (hpointd t)).deriv
  have hqzero (t : ℝ) (ht : R ≤ |t - x|) : q t = 0 :=
    m64BoundaryAveragedCutoff_eq_zero hR N
      ((norm_annulusPoint_sub_lower t x).symm ▸ ht)
  have hq0 : q 0 = 0 := hqzero 0 (by rw [zero_sub, abs_neg, abs_of_pos (hR.trans hx)]; exact hx.le)
  have hqP : q curvePeriod = 0 := hqzero curvePeriod (by
    rw [abs_of_pos (by linarith : 0 < curvePeriod - x)]
    linarith)
  have hqflat (t : ℝ) (ht : t ∈ Icc (x - m64BoundaryCutoffRadius R N / 2)
      (x + m64BoundaryCutoffRadius R N / 2)) : q t = 1 := by
    apply m64BoundaryAveragedCutoff_eq_one hR hN
    change ‖annulusPoint t 0 - annulusPoint x 0‖ ≤ _
    rw [norm_annulusPoint_sub_lower, abs_le]
    constructor <;> linarith [ht.1, ht.2]
  have hql : MonotoneOn q (Iic x) := by
    intro s hs t ht hst
    apply m64BoundaryAveragedCutoff_antitone_radius hR N
    change ‖annulusPoint t 0 - annulusPoint x 0‖ ≤
      ‖annulusPoint s 0 - annulusPoint x 0‖
    rw [norm_annulusPoint_sub_lower, norm_annulusPoint_sub_lower,
      abs_of_nonpos (sub_nonpos.mpr ht), abs_of_nonpos (sub_nonpos.mpr hs)]
    linarith
  have hqr : AntitoneOn q (Ici x) := by
    intro s hs t ht hst
    apply m64BoundaryAveragedCutoff_antitone_radius hR N
    change ‖annulusPoint s 0 - annulusPoint x 0‖ ≤
      ‖annulusPoint t 0 - annulusPoint x 0‖
    rw [norm_annulusPoint_sub_lower, norm_annulusPoint_sub_lower,
      abs_of_nonneg (sub_nonneg.mpr hs), abs_of_nonneg (sub_nonneg.mpr ht)]
    linarith
  have hmono := m64MonotonePhase_cutoff_flux_sq b q hb hq (hR.trans hx)
    (by linarith : x < curvePeriod) (half_pos (m64BoundaryCutoffRadius_pos hR N))
    hq0 hqP (fun t => m64BoundaryAveragedCutoff_le_one a R hN _) hqflat hql hqr
  simp only [hqder] at hmono
  have hdout (p : LoopPlane) (hp : R ≤ ‖p - a‖) : fderiv ℝ eta p = 0 := by
    apply IsLocalMin.fderiv_eq_zero
    exact Filter.Eventually.of_forall (fun y => by
      change eta p ≤ eta y
      rw [show eta p = 0 from m64BoundaryAveragedCutoff_eq_zero hR N hp]
      exact m64BoundaryAveragedCutoff_nonneg a R N y)
  have hleft (s : ℝ) : fderiv ℝ eta (annulusPoint 0 s) e1 = 0 := by
    rw [hdout]
    · rfl
    · have h := PiLp.norm_apply_le (annulusPoint 0 s - a) (0 : Fin 2)
      simp only [a, annulusPoint, PiLp.sub_apply, Matrix.cons_val_zero,
        zero_sub, norm_neg, Real.norm_eq_abs, abs_of_pos (hR.trans hx)] at h
      exact hx.le.trans h
  have hright (s : ℝ) : fderiv ℝ eta (annulusPoint curvePeriod s) e1 = 0 := by
    rw [hdout]
    · rfl
    · have h := PiLp.norm_apply_le (annulusPoint curvePeriod s - a) (0 : Fin 2)
      simp only [a, annulusPoint, PiLp.sub_apply, Matrix.cons_val_zero,
        Real.norm_eq_abs, abs_of_pos (by linarith : 0 < curvePeriod - x)] at h
      exact (by linarith : R ≤ curvePeriod - x).trans h
  have htop (t : ℝ) : fderiv ℝ eta (annulusPoint t 1) e0 = 0 := by
    rw [hdout]
    · rfl
    · have h := PiLp.norm_apply_le (annulusPoint t 1 - a) (1 : Fin 2)
      simp only [a, annulusPoint, PiLp.sub_apply, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, sub_zero, norm_one] at h
      exact hR1.le.trans h
  have hflux := m64WeakPhase_rotated_test_sq_le u V b hV hgreen0 hgreen1 eta heta
    hleft hright htop
  have hcompact : HasCompactSupport eta := by
    apply HasCompactSupport.intro (isCompact_closedBall a R)
    intro p hp
    apply m64BoundaryAveragedCutoff_eq_zero hR N
    exact le_of_lt (by simpa only [Metric.mem_closedBall, dist_eq_norm, not_le] using hp)
  have henergy (i : Fin 2) : (∫ p in S, (fderiv ℝ eta p (EuclideanSpace.single i 1)) ^ 2) ≤
      (∫ p, (fderiv ℝ (m64BoundaryRadialCutoff 0 1) p (EuclideanSpace.single i 1)) ^ 2) / N := by
    have hc : Continuous (fun p => fderiv ℝ eta p (EuclideanSpace.single i 1)) :=
      (heta.continuous_fderiv (by simp)).clm_apply continuous_const
    have hs := hcompact.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)
    have hi : Integrable (fun p => (fderiv ℝ eta p (EuclideanSpace.single i 1)) ^ 2) := by
      apply (hc.pow 2).integrable_of_hasCompactSupport
      simpa only [pow_two] using (hs.mul_right (f' := fun p =>
        fderiv ℝ eta p (EuclideanSpace.single i 1)))
    exact (setIntegral_le_integral hi (Eventually.of_forall (fun p => sq_nonneg _))).trans_eq
      (m64BoundaryAveragedCutoff_column_energy a hR hN i)
  have hEnonneg : 0 ≤ (∫ p in S, (V 0 p) ^ 2) + ∫ p in S, (V 1 p) ^ 2 :=
    add_nonneg (integral_nonneg (fun _ => sq_nonneg _)) (integral_nonneg (fun _ => sq_nonneg _))
  exact (hmono.trans hflux).trans ((mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (add_le_add (henergy 0) (henergy 1)) (by norm_num))
      hEnonneg).trans_eq (by ring))

end PoincareConjecture
