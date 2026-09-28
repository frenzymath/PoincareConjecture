import PoincareConjecture.Definitions.Ch01.RiemannianMetric
import Mathlib.MeasureTheory.Function.Jacobian

set_option autoImplicit false

open scoped ContDiff Topology
open MeasureTheory Set

namespace PoincareConjecture.Proofs.M03

theorem exists_compact_coordinate_change_integral_bound
    {n : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hT : ContDiffOn ℝ 1 T U) (hTi : InjOn T U)
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsCompact K) (hKU : K ⊆ U) :
    letI : MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _
    letI : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : EuclideanSpace ℝ (Fin n) → ℝ,
      ContinuousOn g (T '' K) → (∀ y ∈ T '' K, 0 ≤ g y) →
      (∫ y in T '' K, g y) ≤ C * (∫ x in K, g (T x)) := by
  let : MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _
  let : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
  have hdet : ContinuousOn (fun x => |(fderiv ℝ T x).det|) U :=
    (ContinuousLinearMap.continuous_det.comp_continuousOn
      (hT.continuousOn_fderiv_of_isOpen hU le_rfl)).abs
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (hdet.mono hKU)
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro g hg hg0
  have hTK : ContinuousOn T K := hT.continuousOn.mono hKU
  have hcomp : ContinuousOn (fun x => g (T x)) K :=
    hg.comp hTK (fun x hx => mem_image_of_mem T hx)
  have hweighted : IntegrableOn (fun x => |(fderiv ℝ T x).det| * g (T x)) K :=
    ContinuousOn.integrableOn_compact hK ((hdet.mono hKU).mul hcomp)
  have hupper : IntegrableOn (fun x => max B 0 * g (T x)) K :=
    ContinuousOn.integrableOn_compact hK (continuousOn_const.mul hcomp)
  have hdiff : ∀ x ∈ K, HasFDerivWithinAt T (fderiv ℝ T x) K x := by
    intro x hx
    exact ((hT.differentiableOn (by decide)).differentiableAt
      (hU.mem_nhds (hKU hx))).hasFDerivAt.hasFDerivWithinAt
  have heq := integral_image_eq_integral_abs_det_fderiv_smul volume
    hK.isClosed.measurableSet hdiff (hTi.mono hKU) g
  simp only [smul_eq_mul] at heq
  change (∫ y in T '' K, g y) ≤ max B 0 * (∫ x in K, g (T x))
  rw [heq, ← integral_const_mul]
  apply setIntegral_mono_on hweighted hupper hK.isClosed.measurableSet
  intro x hx
  have hbound : |(fderiv ℝ T x).det| ≤ max B 0 := by
    simpa only [Real.norm_eq_abs, abs_abs] using (hB x hx).trans (le_max_left B 0)
  exact mul_le_mul_of_nonneg_right hbound (hg0 _ (mem_image_of_mem T hx))

end PoincareConjecture.Proofs.M03
