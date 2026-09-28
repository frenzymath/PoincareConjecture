import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct











set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M47



theorem exists_jointSeed_global_radial_extension
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (gamma : ℝ → M)
    (hgamma : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ gamma (Ioo (-epsilon) (1 + epsilon))) :
    ∃ beta : ℝ → M, ContMDiff (𝓘(ℝ, ℝ)) (𝓡 n) ∞ beta ∧
      ∀ s ∈ Icc (0 : ℝ) 1, beta =ᶠ[𝓝 s] gamma := by
  let chi : ContDiffBump (1 / 2 : ℝ) :=
    ⟨1 / 2 + epsilon / 2, 1 / 2 + epsilon, by positivity, by linarith⟩
  let kappa (s : ℝ) := chi s * s + (1 - chi s) / 2
  have hkappa : ContDiff ℝ ∞ kappa :=
    (chi.contDiff.mul contDiff_id).add ((contDiff_const.sub chi.contDiff).div_const 2)
  have hinto (s : ℝ) : kappa s ∈ Ioo (-epsilon) (1 + epsilon) := by
    by_cases hchi : chi s = 0
    · simp only [kappa, hchi, zero_mul, sub_zero, zero_add]
      constructor <;> linarith
    · have hsball : s ∈ Metric.ball (1 / 2 : ℝ) chi.rOut := by
        rw [← chi.support_eq]
        exact hchi
      have hsabs : |s - 1 / 2| < 1 / 2 + epsilon := hsball
      obtain ⟨hslo, hshi⟩ := abs_lt.1 hsabs
      have hpos : 0 < chi s := lt_of_le_of_ne chi.nonneg (Ne.symm hchi)
      have hle : chi s ≤ 1 := chi.le_one
      have hlo := mul_pos hpos (show 0 < s + epsilon by linarith)
      have hhi := mul_pos hpos (show 0 < 1 + epsilon - s by linarith)
      have hrest := mul_nonneg (sub_nonneg.mpr hle)
        (show 0 ≤ 1 / 2 + epsilon by linarith)
      dsimp only [kappa]
      constructor <;> nlinarith
  refine ⟨gamma ∘ kappa, ?_, ?_⟩
  · intro s
    exact ((hgamma (kappa s) (hinto s)).contMDiffAt
      (isOpen_Ioo.mem_nhds (hinto s))).comp s hkappa.contMDiff.contMDiffAt
  · intro s hs
    have hsball : s ∈ Metric.ball (1 / 2 : ℝ) chi.rIn := by
      change |s - 1 / 2| < 1 / 2 + epsilon / 2
      rw [abs_lt]
      constructor <;> linarith [hs.1, hs.2]
    filter_upwards [chi.eventuallyEq_one_of_mem_ball hsball] with t ht
    change gamma (chi t * t + (1 - chi t) / 2) = gamma t
    rw [show chi t = 1 from ht]
    simp

end PoincareConjecture.M47
