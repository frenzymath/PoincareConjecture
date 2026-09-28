import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityEulerReconstruction
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.ChartMetricRealization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold

universe u

namespace PoincareConjecture.M65Euler

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M] {N : ℕ}

theorem reconstruction_pairing (g : RiemannianMetric 3 M)
    (e : M → EuclideanSpace ℝ (Fin N)) (ψ : EuclideanSpace ℝ (Fin 3) → M)
    (y : EuclideanSpace ℝ (Fin 3))
    (he : MDifferentiableAt (𝓡 3) (𝓡 N) e (ψ y))
    (hψ : MDifferentiableAt (𝓡 3) (𝓡 3) ψ y)
    (hinj : Function.Injective (mfderiv (𝓡 3) (𝓡 N) e (ψ y)))
    (v w : EuclideanSpace ℝ (Fin 3)) :
    m65EmbeddingMetric g e (ψ y) (fderiv ℝ (e ∘ ψ) y v) (fderiv ℝ (e ∘ ψ) y w) =
      g.inner (ψ y) (mfderiv (𝓡 3) (𝓡 3) ψ y v) (mfderiv (𝓡 3) (𝓡 3) ψ y w) := by
  have hd : fderiv ℝ (e ∘ ψ) y =
      (mfderiv (𝓡 3) (𝓡 N) e (ψ y)).comp (mfderiv (𝓡 3) (𝓡 3) ψ y) := by
    rw [← mfderiv_eq_fderiv]
    exact mfderiv_comp y he hψ
  rw [hd]
  exact m65EmbeddingMetric_image g e (ψ y) hinj _ _

theorem exists_chart_energy_metric (g : RiemannianMetric 3 M)
    (e : M → EuclideanSpace ℝ (Fin N)) (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ p, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e p)) (p : M) :
    ∃ (gE : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3))) (_DE : LeviCivitaData gE)
      (W : Set (EuclideanSpace ℝ (Fin 3))),
      IsOpen W ∧ extChartAt (𝓡 3) p p ∈ W ∧ W ⊆ (extChartAt (𝓡 3) p).target ∧
      ∀ y ∈ W, ∀ v w : EuclideanSpace ℝ (Fin 3),
        m65EmbeddingMetric g e ((extChartAt (𝓡 3) p).symm y)
          (fderiv ℝ (e ∘ (extChartAt (𝓡 3) p).symm) y v)
          (fderiv ℝ (e ∘ (extChartAt (𝓡 3) p).symm) y w) = gE.inner y v w := by
  let c := extChartAt (𝓡 3) p
  obtain ⟨gE, DE, hmetric⟩ := m65Exists_chartMetric g p
  have htarget : ∀ᶠ y in 𝓝 (c p), y ∈ c.target := extChartAt_target_mem_nhds (I := 𝓡 3) p
  obtain ⟨W, hW, hWo, hpW⟩ := mem_nhds_iff.mp (htarget.and hmetric)
  refine ⟨gE, DE, W, hWo, hpW, fun y hy => (hW hy).1, ?_⟩
  intro y hy v w
  have hψ : MDifferentiableAt (𝓡 3) (𝓡 3) c.symm y :=
    ((contMDiffWithinAt_extChartAt_symm_target (n := ∞) p (hW hy).1).contMDiffAt
      (extChartAt_target_mem_nhds' (hW hy).1)).mdifferentiableAt (by simp)
  rw [reconstruction_pairing g e c.symm y
    (he.contMDiffAt.mdifferentiableAt (by simp)) hψ (hinj _) v w]
  exact ((hW hy).2 v w).symm

end PoincareConjecture.M65Euler
