import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundarySeamMonotoneFlux

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

theorem m64WeakPhase_rotated_seam_test_identity
    (u : LoopPlane → ℝ) (V : Fin 2 → LoopPlane → ℝ) (b : ℝ → ℝ) (D : ℝ)
    (hseam : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∀ s ∈ Icc (0 : ℝ) 1, phi (annulusPoint curvePeriod s) = phi (annulusPoint 0 s)) →
      (∫ p in S, phi p * V 0 p) + (∫ p in S, fderiv ℝ phi p e0 * u p) =
        D * ∫ s in Icc (0 : ℝ) 1, phi (annulusPoint curvePeriod s))
    (hgreen1 : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∀ x : ℝ, phi (annulusPoint x 1) = 0) →
      (∫ p in S, phi p * V 1 p) + (∫ p in S, fderiv ℝ phi p e1 * u p) =
        -(∫ x in Icc (0 : ℝ) curvePeriod, phi (annulusPoint x 0) * b x))
    (eta : LoopPlane → ℝ) (heta : ContDiff ℝ ∞ eta)
    (hperiod : ∀ s ∈ Icc (0 : ℝ) 1,
      fderiv ℝ eta (annulusPoint curvePeriod s) e1 = fderiv ℝ eta (annulusPoint 0 s) e1)
    (htop : ∀ x : ℝ, fderiv ℝ eta (annulusPoint x 1) e0 = 0)
    (hzero : eta (annulusPoint curvePeriod 0) = 1)
    (hone : eta (annulusPoint curvePeriod 1) = 0) :
    D - (∫ x in Icc (0 : ℝ) curvePeriod, fderiv ℝ eta (annulusPoint x 0) e0 * b x) =
      (∫ p in S, fderiv ℝ eta p e0 * V 1 p) -
        ∫ p in S, fderiv ℝ eta p e1 * V 0 p := by
  let d : Fin 2 → LoopPlane → ℝ := fun i p =>
    fderiv ℝ eta p (EuclideanSpace.single i 1)
  have hd (i : Fin 2) : ContDiff ℝ 1 (d i) :=
    (heta.fderiv_right (m := 1) (by norm_cast : (1 : ℕ∞ω) + 1 ≤ ∞)).clm_apply
      contDiff_const
  have hfd (p : LoopPlane) : DifferentiableAt ℝ (fderiv ℝ eta) p :=
    ((heta.contDiffAt).fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hswap (p : LoopPlane) : fderiv ℝ (d 1) p e0 = fderiv ℝ (d 0) p e1 := by
    have hsymm := (heta.contDiffAt (x := p)).isSymmSndFDerivAt (by
      rw [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.mpr le_top) e0 e1
    change fderiv ℝ (fderiv ℝ eta) p e0 e1 =
      fderiv ℝ (fderiv ℝ eta) p e1 e0 at hsymm
    dsimp only [d]
    rw [fderiv_clm_apply (hfd p) (differentiableAt_const e1),
      fderiv_clm_apply (hfd p) (differentiableAt_const e0)]
    simpa using hsymm
  have hpoint : (fun s : ℝ => annulusPoint curvePeriod s) =
      (fun s : ℝ => curvePeriod • e0 + s • e1) := by
    ext s i
    fin_cases i <;> simp [annulusPoint]
  have hpointd (s : ℝ) : HasDerivAt (fun s : ℝ => annulusPoint curvePeriod s) e1 s := by
    rw [hpoint]
    simpa using ((hasDerivAt_id s).smul_const e1).const_add (curvePeriod • e0)
  have hpointc : Continuous (fun s : ℝ => annulusPoint curvePeriod s) := by
    rw [hpoint]
    exact continuous_const.add (continuous_id.smul continuous_const)
  have hside : (∫ s in Icc (0 : ℝ) 1, d 1 (annulusPoint curvePeriod s)) = -1 := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
    have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => (heta.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt s
        (hpointd s)) (((hd 1).continuous.comp hpointc).intervalIntegrable 0 1)
    simpa only [Function.comp_apply, hzero, hone, zero_sub, d] using hh
  have h0 := hseam (d 1) (hd 1) hperiod
  have h1 := hgreen1 (d 0) (hd 0) htop
  rw [hside, mul_neg_one] at h0
  simp only [hswap] at h0
  change D - (∫ x in Icc (0 : ℝ) curvePeriod, d 0 (annulusPoint x 0) * b x) =
    (∫ p in S, d 0 p * V 1 p) - ∫ p in S, d 1 p * V 0 p
  linarith

theorem m64WeakPhase_rotated_seam_test_sq_le
    (u : LoopPlane → ℝ) (V : Fin 2 → LoopPlane → ℝ) (b : ℝ → ℝ) (D : ℝ)
    (hV : ∀ i, MemLp (V i) 2 mu)
    (hseam : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∀ s ∈ Icc (0 : ℝ) 1, phi (annulusPoint curvePeriod s) = phi (annulusPoint 0 s)) →
      (∫ p in S, phi p * V 0 p) + (∫ p in S, fderiv ℝ phi p e0 * u p) =
        D * ∫ s in Icc (0 : ℝ) 1, phi (annulusPoint curvePeriod s))
    (hgreen1 : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∀ x : ℝ, phi (annulusPoint x 1) = 0) →
      (∫ p in S, phi p * V 1 p) + (∫ p in S, fderiv ℝ phi p e1 * u p) =
        -(∫ x in Icc (0 : ℝ) curvePeriod, phi (annulusPoint x 0) * b x))
    (eta : LoopPlane → ℝ) (heta : ContDiff ℝ ∞ eta)
    (hperiod : ∀ s ∈ Icc (0 : ℝ) 1,
      fderiv ℝ eta (annulusPoint curvePeriod s) e1 = fderiv ℝ eta (annulusPoint 0 s) e1)
    (htop : ∀ x : ℝ, fderiv ℝ eta (annulusPoint x 1) e0 = 0)
    (hzero : eta (annulusPoint curvePeriod 0) = 1)
    (hone : eta (annulusPoint curvePeriod 1) = 0) :
    (D - ∫ x in Icc (0 : ℝ) curvePeriod,
      fderiv ℝ eta (annulusPoint x 0) e0 * b x) ^ 2 ≤
      2 * ((∫ p in S, (fderiv ℝ eta p e0) ^ 2) +
        ∫ p in S, (fderiv ℝ eta p e1) ^ 2) *
        ((∫ p in S, (V 0 p) ^ 2) + ∫ p in S, (V 1 p) ^ 2) := by
  have hd (i : Fin 2) : MemLp (fun p =>
      fderiv ℝ eta p (EuclideanSpace.single i 1)) 2 mu := by
    have hc : Continuous (fun p => fderiv ℝ eta p (EuclideanSpace.single i 1)) :=
      (heta.continuous_fderiv (by simp)).clm_apply continuous_const
    apply (memLp_two_iff_integrable_sq hc.aestronglyMeasurable).mpr
    exact (hc.pow 2).continuousOn.integrableOn_compact
      m64AnnulusDomain_isCompact |>.mono_set interior_subset
  rw [m64WeakPhase_rotated_seam_test_identity u V b D hseam hgreen1 eta heta
    hperiod htop hzero hone]
  have h0 := M64Uniformization.scalar_integral_mul_sq_le (hd 1) (hV 0)
  have h1 := M64Uniformization.scalar_integral_mul_sq_le (hd 0) (hV 1)
  have hn (f : LoopPlane → ℝ) : 0 ≤ ∫ p in S, f p ^ 2 :=
    integral_nonneg (fun p => sq_nonneg _)
  nlinarith [sq_nonneg ((∫ p in S, fderiv ℝ eta p e1 * V 0 p) +
    ∫ p in S, fderiv ℝ eta p e0 * V 1 p),
    mul_nonneg (hn (fun p => fderiv ℝ eta p e0)) (hn (V 0)),
    mul_nonneg (hn (fun p => fderiv ℝ eta p e1)) (hn (V 1))]

end PoincareConjecture
