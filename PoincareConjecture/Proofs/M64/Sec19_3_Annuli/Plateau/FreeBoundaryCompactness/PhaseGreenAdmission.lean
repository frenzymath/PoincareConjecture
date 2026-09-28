import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.PhaseLipschitz
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.PhaseBoundaryIdentities
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.LipschitzVectorGreen










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal NNReal

namespace PoincareConjecture.M64

open Poincare.Analysis.Sobolev.Weak

local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S
local notation "e0" => EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
local notation "e1" => EuclideanSpace.single (1 : Fin 2) (1 : ℝ)

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}




theorem annulus_exists_real_weak_phase
    (P : M62.CircleProductData F circumference) (t : ℝ)
    {c0 c1 : ℝ → P.charts.Point} (A : M64Annulus (P.flow.metric t) c0 c1)
    (hA : ContMDiffOn (𝓡 2) (𝓡 (n + 1)) 1 A.map S)
    (L0 L1 : ℝ → ℝ) (hL0 : Continuous L0) (hL1 : Continuous L1)
    (hzero : ∀ x ∈ Icc (0 : ℝ) curvePeriod, P.circle.quotient (L0 x) = (c0 x).2)
    (hone : ∀ x ∈ Icc (0 : ℝ) curvePeriod, P.circle.quotient (L1 x) = (c1 x).2)
    {D : ℝ} (hdegree : L0 curvePeriod = L0 0 + D) :
    ∃ (L : LoopPlane → ℝ) (k : ℤ),
      Continuous L ∧ ContDiffOn ℝ 1 L S ∧ MemLp L 2 mu ∧
      (∀ i : Fin 2,
        MemLp (fun p => fderiv ℝ L p (EuclideanSpace.single i 1)) 2 mu ∧
        HasWeakPartialDeriv i (fun p => fderiv ℝ L p (EuclideanSpace.single i 1)) L S) ∧
      (∀ p ∈ m64AnnulusDomain, P.circle.quotient (L p) = (A.map p).2) ∧
      (∀ x ∈ Icc (0 : ℝ) curvePeriod, L (annulusPoint x 0) = L0 x) ∧
      (∀ x ∈ Icc (0 : ℝ) curvePeriod,
        L (annulusPoint x 1) = L1 x + k * circumference) ∧
      (∀ s ∈ Icc (0 : ℝ) 1,
        L (annulusPoint curvePeriod s) = L (annulusPoint 0 s) + D) ∧
      (∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
        (∫ p in S, phi p * fderiv ℝ L p e1) +
          (∫ p in S, fderiv ℝ phi p e1 * L p) =
            ∫ x in Icc (0 : ℝ) curvePeriod,
              phi (annulusPoint x 1) * (L1 x + k * circumference) -
                phi (annulusPoint x 0) * L0 x) ∧
      (∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
        (∀ s ∈ Icc (0 : ℝ) 1,
          phi (annulusPoint curvePeriod s) = phi (annulusPoint 0 s)) →
        (∫ p in S, phi p * fderiv ℝ L p e0) +
          (∫ p in S, fderiv ℝ phi p e0 * L p) =
            D * ∫ s in Icc (0 : ℝ) 1, phi (annulusPoint 0 s)) := by
  obtain ⟨L, hL, hLreg, hquot, hlower, -⟩ :=
    annulus_exists_continuous_phase_with_gradient_bound P t A hA L0 hL0 hzero
  have hLip := annulus_phase_lipschitzOn P t A hA L hL hLreg hquot
  have htop : ∀ x ∈ Icc (0 : ℝ) curvePeriod,
      P.circle.quotient (L1 x) = (A.map (annulusPoint x 1)).2 := by
    intro x hx
    rw [A.upper_boundary]
    exact hone x hx
  obtain ⟨k, hupper⟩ := closed_rectangle_phase_upper_integer P.circle
    (fun p => (A.map p).2) L hL hquot L1 hL1 htop
  have hP : 0 ≤ curvePeriod := by unfold curvePeriod; positivity
  have hseam : ∀ s ∈ Icc (0 : ℝ) 1,
      L (annulusPoint curvePeriod s) = L (annulusPoint 0 s) + D := by
    apply closed_rectangle_phase_affine_seam P.circle (fun p => (A.map p).2)
      L hL hquot
    · intro s _
      simpa only [zero_add] using congrArg Prod.snd (A.periodic 0 s)
    · rw [hlower curvePeriod ⟨hP, le_rfl⟩, hlower 0 ⟨le_rfl, hP⟩]
      exact hdegree
  refine ⟨L, k, hL, hLreg, m64_lipschitz_memLp_two hLip, ?_,
    hquot, hlower, hupper, hseam, ?_, ?_⟩
  · intro i
    let : IsFiniteMeasure mu := ⟨by
      rw [Measure.restrict_apply_univ]
      exact (measure_mono interior_subset).trans_lt m64AnnulusDomain_isCompact.measure_lt_top⟩
    exact ⟨(memLp_top_fderiv_apply_of_lipschitzOn isOpen_interior
      (hLip.mono interior_subset) (EuclideanSpace.single i 1)).mono_exponent le_top,
      m64_lipschitz_scalar_weak_partial hLip i⟩
  · intro phi hphi
    rw [m64Annulus_vertical_green_lipschitzOn hLip hphi]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    rw [hupper x hx, hlower x hx]
  · intro phi hphi hperiodic
    rw [m64Annulus_horizontal_green_lipschitzOn hLip hphi, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    rw [hseam s hs, hperiodic s hs]
    ring

end PoincareConjecture.M64
