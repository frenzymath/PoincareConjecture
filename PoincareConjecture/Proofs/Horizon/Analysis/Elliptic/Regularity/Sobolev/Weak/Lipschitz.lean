import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Sobolev.Weak.Derivatives
import Mathlib.Analysis.Calculus.Rademacher








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Manifold
open scoped Manifold ContDiff Bundle Topology ENNReal NNReal

namespace Poincare.Analysis.Sobolev.Weak

variable {n : ℕ}


theorem hasWeakPartialDeriv_lineDeriv_of_lipschitz
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {C : ℝ≥0} (hf : LipschitzWith C f)
    {O : Set (EuclideanSpace ℝ (Fin n))} (i : Fin n) :
    HasWeakPartialDeriv i
      (fun x => lineDeriv ℝ f x (EuclideanSpace.single i 1)) f O := by
  intro φ hφ hc hs
  let v : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i 1
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hφ (by simp)
  have hp := hf.integral_lineDeriv_mul_eq (μ := volume) hL hc v
  have hline (x : EuclideanSpace ℝ (Fin n)) :
      lineDeriv ℝ φ x v = fderiv ℝ φ x v :=
    (hφ.differentiable (by simp) x).lineDeriv_eq_fderiv
  simp_rw [lineDeriv_neg, hline, neg_mul, integral_neg] at hp
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero,
    setIntegral_eq_integral_of_forall_compl_eq_zero]
  · have hcomm : (∫ x, f x * fderiv ℝ φ x v) =
        ∫ x, fderiv ℝ φ x v * f x := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => mul_comm _ _
    change (∫ x, f x * fderiv ℝ φ x v) =
      -(∫ x, lineDeriv ℝ f x v * φ x)
    rw [hcomm]
    linarith
  · intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (hs ht)), mul_zero]
  · intro x hx
    have hz : fderiv ℝ φ x (EuclideanSpace.single i 1) = 0 :=
      image_eq_zero_of_notMem_tsupport
        (f := fun y => fderiv ℝ φ y (EuclideanSpace.single i 1))
        (fun ht => hx (hs (tsupport_fderiv_apply_subset ℝ _ ht)))
    rw [hz, mul_zero]



theorem exists_weakPartials_of_lipschitzOn
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {O : Set (EuclideanSpace ℝ (Fin n))} (hO : IsOpen O)
    {C : ℝ≥0} (hf : LipschitzOnWith C f O) :
    (∀ K, IsCompact K → K ⊆ O → MemLp f 2 (volume.restrict K)) ∧
    ∃ p : Fin n → EuclideanSpace ℝ (Fin n) → ℝ,
      (∀ i K, IsCompact K → K ⊆ O → MemLp (p i) 2 (volume.restrict K)) ∧
      ∀ i, HasWeakPartialDeriv i (p i) f O := by
  obtain ⟨F, hF, heq⟩ := hf.extend_real
  constructor
  · intro K hK hKO
    let : IsFiniteMeasure (volume.restrict K) := ⟨by
      simpa only [Measure.restrict_apply_univ] using hK.measure_lt_top (μ := volume)⟩
    obtain ⟨B, hB⟩ := hK.bddAbove_image (hf.continuousOn.mono hKO).norm
    have htop : MemLp f ∞ (volume.restrict K) := by
      apply memLp_top_of_bound
        ((hf.continuousOn.mono hKO).aestronglyMeasurable hK.measurableSet) B
      filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
      exact hB (mem_image_of_mem _ hx)
    exact htop.mono_exponent le_top
  · refine ⟨fun i x => lineDeriv ℝ F x (EuclideanSpace.single i 1), ?_, ?_⟩
    · intro i K hK _
      let : IsFiniteMeasure (volume.restrict K) := ⟨by
        simpa only [Measure.restrict_apply_univ] using hK.measure_lt_top (μ := volume)⟩
      exact (hF.memLp_lineDeriv (μ := volume.restrict K)
        (EuclideanSpace.single i 1)).mono_exponent le_top
    · intro i φ hφ hc hs
      rw [setIntegral_congr_fun hO.measurableSet
        (fun x hx => congrArg (fun z => z * fderiv ℝ φ x (EuclideanSpace.single i 1))
          (heq hx))]
      exact hasWeakPartialDeriv_lineDeriv_of_lipschitz hF i φ hφ hc hs

end Poincare.Analysis.Sobolev.Weak
