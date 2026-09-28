import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundarySeamCutoff












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace PoincareConjecture

local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S
local notation "e0" => EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
local notation "e1" => EuclideanSpace.single (1 : Fin 2) (1 : ℝ)




theorem m64WeakPhase_monotone_seam_gap_sq_le
    (u : LoopPlane → ℝ) (V : Fin 2 → LoopPlane → ℝ) (b : ℝ → ℝ) (D : ℝ)
    (hV : ∀ i, MemLp (V i) 2 mu) (hb : Monotone b)
    (hbperiod : ∀ x, b (x + curvePeriod) = b x + D)
    (hseam : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∀ s ∈ Icc (0 : ℝ) 1, phi (annulusPoint curvePeriod s) = phi (annulusPoint 0 s)) →
      (∫ p in S, phi p * V 0 p) + (∫ p in S, fderiv ℝ phi p e0 * u p) =
        D * ∫ s in Icc (0 : ℝ) 1, phi (annulusPoint curvePeriod s))
    (hgreen1 : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∀ x : ℝ, phi (annulusPoint x 1) = 0) →
      (∫ p in S, phi p * V 1 p) + (∫ p in S, fderiv ℝ phi p e1 * u p) =
        -(∫ x in Icc (0 : ℝ) curvePeriod, phi (annulusPoint x 0) * b x))
    {R : ℝ} (hR : 0 < R) (hRP : 2 * R < curvePeriod) (hR1 : R < 1)
    {N : ℕ} (hN : 0 < N) :
    (b (m64BoundaryCutoffRadius R N / 2) -
      b (-(m64BoundaryCutoffRadius R N / 2))) ^ 2 ≤
      (8 * ((∫ p, (fderiv ℝ (m64BoundaryRadialCutoff 0 1) p e0) ^ 2) +
        ∫ p, (fderiv ℝ (m64BoundaryRadialCutoff 0 1) p e1) ^ 2) *
        ((∫ p in S, (V 0 p) ^ 2) + ∫ p in S, (V 1 p) ^ 2)) / N := by
  let eta := m64BoundarySeamCutoff R N
  let q : ℝ → ℝ := fun t => eta (annulusPoint t 0)
  have heta : ContDiff ℝ ∞ eta := m64BoundarySeamCutoff_contDiff R N
  have hpoint : (fun t : ℝ => annulusPoint t 0) = (fun t : ℝ => t • e0) := by
    ext t i
    fin_cases i <;> simp [annulusPoint]
  have hq : ContDiff ℝ 1 q := (heta.of_le (by norm_cast : (1 : ℕ∞ω) ≤ ∞)).comp
    (by rw [hpoint]; exact contDiff_id.smul contDiff_const)
  have hpointd (t : ℝ) : HasDerivAt (fun t : ℝ => annulusPoint t 0) e0 t := by
    rw [hpoint]
    simpa using (hasDerivAt_id t).smul_const e0
  have hqder (t : ℝ) : deriv q t = fderiv ℝ eta (annulusPoint t 0) e0 :=
    ((heta.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t (hpointd t)).deriv
  obtain ⟨hq0, hqP, hqmid, hf0, hfP, hql, hqr⟩ :=
    m64BoundarySeamCutoff_bottom_profile hR hRP hN
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  have hmono := m64MonotonePhase_seam_cutoff_flux_sq b q hb hq
    (half_pos hP) (half_lt_self hP) (half_pos (m64BoundaryCutoffRadius_pos hR N))
    hq0 hqP hqmid (fun t => m64BoundarySeamCutoff_le_one hR hRP hN _) hf0 hfP hql hqr
    (by simpa only [neg_add_eq_sub] using hbperiod (-(m64BoundaryCutoffRadius R N / 2)))
  simp only [hqder] at hmono
  have hflux := m64WeakPhase_rotated_seam_test_sq_le u V b D hV hseam hgreen1 eta heta
    (fun s _ => m64BoundarySeamCutoff_periodic_derivative hR (by linarith) N s)
    (fun t => by rw [m64BoundarySeamCutoff_top_fderiv hR hR1]; rfl)
    hqP (m64BoundarySeamCutoff_top_zero hR hR1 N curvePeriod)
  have henergy (i : Fin 2) := m64BoundarySeamCutoff_column_energy_le hR hN i
  have hEnonneg : 0 ≤ (∫ p in S, (V 0 p) ^ 2) + ∫ p in S, (V 1 p) ^ 2 :=
    add_nonneg (integral_nonneg (fun _ => sq_nonneg _)) (integral_nonneg (fun _ => sq_nonneg _))
  exact (hmono.trans hflux).trans ((mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (add_le_add (henergy 0) (henergy 1)) (by norm_num))
      hEnonneg).trans_eq (by ring))

end PoincareConjecture
