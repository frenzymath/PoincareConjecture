import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Compactness.ChartEnergy
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Compactness.ChartL2
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Compactness.Localization
import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.Euclidean.Rellich
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Dirichlet.SequentialCompactness








set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff

namespace PoincareConjecture.LeviCivitaData.Dirichlet

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {D : LeviCivitaData g} {Ω : Set M}



theorem exists_cauchySeq_testToL2_of_chart_support
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {K : Set M} (hK : IsCompact K) (hKs : K ⊆ e.target)
    (f : ℕ → EnergyTest D Ω) (hf : ∀ k, tsupport (f k : M → ℝ) ⊆ K)
    {R : ℝ} (hR : 0 ≤ R) (hb : ∀ k, ‖f k‖ ≤ R) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ CauchySeq (fun k => testToL2 D Ω (f (φ k))) := by
  obtain ⟨A, hA, hAb⟩ := exists_integral_chart_sq_le_energy (D := D) (Ω := Ω) e he hei hK hKs
  obtain ⟨B, hB, hBb⟩ := exists_integral_chart_fderiv_sq_le_energy
    (D := D) (Ω := Ω) e he hei hK hKs
  have hn (k : ℕ) : ‖f k‖ ^ 2 ≤ R ^ 2 := (sq_le_sq₀ (norm_nonneg _) hR).mpr (hb k)
  obtain ⟨φ, hφ, hc⟩ := Poincare.Analysis.Sobolev.rellich_smooth_common_compact_support_cauchySeq
    (hK.image_of_continuousOn (e.symm.continuousOn.mono hKs))
    (fun k => (contDiff_chartPullback e he (f k).smooth (f k).hasCompactSupport
      ((hf k).trans hKs)).of_le (by simp))
    (fun k => (tsupport_chartPullback_subset_image e (f k).hasCompactSupport
      ((hf k).trans hKs)).trans (image_mono (hf k)))
    (fun k => (f k).chartPullback_memLp e he ((hf k).trans hKs))
    (fun k => (hAb (f k) (hf k)).trans (mul_le_mul_of_nonneg_left (hn k) hA))
    (fun k => (hBb (f k) (hf k)).trans (mul_le_mul_of_nonneg_left (hn k) hB))
  exact ⟨φ, hφ, cauchySeq_testToL2_of_chartToL2 e he hei hK hKs
    (fun k => f (φ k)) (fun k => hf (φ k)) hc⟩



theorem isCompactOperator_testToL2_mulSmooth
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    (χ : M → ℝ) (hχ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ e.target) :
    IsCompactOperator ((testToL2CLM D Ω).comp (mulSmoothCLM D Ω χ hχ hc)) := by
  apply Poincare.Analysis.Dirichlet.isCompactOperator_of_cauchySeq_subseq
  intro f hf
  obtain ⟨C, hC, hbound⟩ := exists_mulSmooth_norm_bound (D := D) (Ω := Ω) χ hχ hc
  obtain ⟨φ, hφ, hlim⟩ := exists_cauchySeq_testToL2_of_chart_support e he hei hc hs
    (fun k => (f k).mulSmooth χ hχ) (fun k => (f k).mulSmooth_support_subset χ hχ)
    hC (fun k => (hbound (f k)).trans (by nlinarith [hf k]))
  exact ⟨φ, hφ, hlim⟩

end PoincareConjecture.LeviCivitaData.Dirichlet
