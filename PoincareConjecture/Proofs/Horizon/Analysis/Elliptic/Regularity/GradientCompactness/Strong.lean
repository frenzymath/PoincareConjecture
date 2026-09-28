import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.GradientCompactness.Cauchy
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.GradientCompactness.Identification








noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal BigOperators

namespace Poincare.Analysis.Elliptic

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)


theorem memLp_two_of_lipschitzOn_compact_closure
    {O U : Set E} (hU : IsOpen U) (hUc : IsCompact (closure U))
    (hclUO : closure U ⊆ O) {u : E → ℝ} {L : ℝ≥0}
    (hu : LipschitzOnWith L u O) : MemLp u 2 (volume.restrict U) := by
  let : IsFiniteMeasure (volume.restrict U) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact (measure_mono subset_closure).trans_lt hUc.measure_lt_top⟩
  obtain ⟨B, hB⟩ := hUc.bddAbove_image (hu.continuousOn.mono hclUO).norm
  have ht : MemLp u ∞ (volume.restrict U) := by
    apply memLp_top_of_bound
      ((hu.continuousOn.mono (subset_closure.trans hclUO)).aestronglyMeasurable
        hU.measurableSet) B
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    exact hB (mem_image_of_mem _ (subset_closure hx))
  exact ht.mono_exponent le_top



theorem tendsto_lipschitzPartialL2_of_weak_divergence
    {O U : Set E} (hO : IsOpen O) (hU : IsOpen U)
    (hUc : IsCompact (closure U)) (hclUO : closure U ⊆ O)
    [IsFiniteMeasure (volume.restrict O)] [IsFiniteMeasure (volume.restrict U)]
    {u : ℕ → E → ℝ} {v : E → ℝ}
    {F : ℕ → Fin d → E → ℝ} {f : ℕ → E → ℝ}
    {A : ℕ → E → Fin d → Fin d → ℝ} {L : ℝ≥0} {c C D : ℝ}
    (hc : 0 < c) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hu : ∀ k, LipschitzOnWith L (u k) O)
    (hlim : TendstoUniformlyOn u v atTop O) (hAc : UniformCauchySeqOn A atTop O)
    (hF : ∀ k i, MemLp (F k i) 2 (volume.restrict O))
    (hf : ∀ k, MemLp (f k) 2 (volume.restrict O))
    (hfC : ∀ k x, x ∈ O → |f k x| ≤ C)
    (hFC : ∀ k i x, x ∈ O → |F k i x| ≤ C)
    (hell : ∀ k x, x ∈ O → ∀ w : Fin d → ℝ,
      c * ∑ i, (w i) ^ 2 ≤ ∑ i, ∑ j, A k x i j * w j * w i)
    (hFid : ∀ k x, x ∈ O → ∀ i, F k i x =
      -(∑ j, A k x i j * fderiv ℝ (u k) x (EuclideanSpace.single j 1)))
    (hle : ∀ k (ψ : E → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ O → (∀ x, 0 ≤ ψ x) →
      (∫ x in O, ∑ i, F k i x * fderiv ℝ ψ x (EuclideanSpace.single i 1)) ≤
        ∫ x in O, f k x * ψ x)
    {φ : E → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hφO : tsupport φ ⊆ O) (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∀ x, φ x ≤ 1)
    (hφU : ∀ x ∈ U, φ x = 1)
    (hdφ : ∀ i x, x ∈ O → |fderiv ℝ φ x (EuclideanSpace.single i 1)| ≤ D)
    (i : Fin d) :
    Tendsto (fun k => lipschitzPartialL2 hU
      ((hu k).mono (subset_closure.trans hclUO)) i) atTop
      (𝓝 (lipschitzPartialL2 hU
        ((lipschitzOnWith_of_tendstoUniformlyOn hu hlim).mono
          (subset_closure.trans hclUO)) i)) := by
  have hUO : U ⊆ O := subset_closure.trans hclUO
  have hv := lipschitzOnWith_of_tendstoUniformlyOn hu hlim
  have hCauchy := cauchySeq_lipschitzPartialL2_of_weak_divergence hO hU hUO hc hC hD
    hu hlim.uniformCauchySeqOn hAc hF hf hfC hFC hell hFid hle hφ hφc hφO hφ0 hφ1 hφU hdφ i
  exact tendsto_lipschitzPartialL2_of_cauchy hU (fun k => (hu k).mono hUO) (hv.mono hUO)
    (fun k => memLp_two_of_lipschitzOn_compact_closure hU hUc hclUO (hu k))
    (memLp_two_of_lipschitzOn_compact_closure hU hUc hclUO hv) (hlim.mono hUO) i hCauchy

end Poincare.Analysis.Elliptic
