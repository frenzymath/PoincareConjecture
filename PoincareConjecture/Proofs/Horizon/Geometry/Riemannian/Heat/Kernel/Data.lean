import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Exhaustion

set_option autoImplicit false

open MeasureTheory Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

structure ConservativeHeatKernelData (g : RiemannianMetric n M) where
  connection : LeviCivitaData g
  kernel : M → M → ℝ → ℝ
  positive : ∀ x y t, 0 < t → 0 < kernel x y t
  smooth : ∀ x y t, 0 < t →
    ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun z => kernel z y t) x
  timeDifferentiable : ∀ x y t, 0 < t →
    DifferentiableAt ℝ (fun s => kernel x y s) t
  mass_one : ∀ x t, 0 < t →
    ∫ y, kernel x y t ∂volumeMeasure g = 1
  initial : ∀ (φ : M → ℝ), Continuous φ → HasCompactSupport φ →
    ∀ x, Tendsto (fun t => ∫ y, kernel x y t * φ y ∂volumeMeasure g)
      (𝓝[>] 0) (𝓝 (φ x))
  heat_equation : ∀ x y t, 0 < t →
    deriv (fun s => kernel x y s) t =
      connection.laplacian (fun z => kernel z y t) x
  first_moment_integrable : ∀ x t, 0 < t →
    Integrable (fun y => (g.edist x y).toReal * kernel x y t)
      (volumeMeasure g)
  first_moment_bound : ∃ C : ℝ, 0 < C ∧
    ∀ x t, 0 < t → t ≤ 1 →
      ∫ y, (g.edist x y).toReal * kernel x y t ∂volumeMeasure g ≤ C
  first_moment_tendsto_zero :
    Tendsto (fun t => ⨆ x, ∫ y, (g.edist x y).toReal * kernel x y t
      ∂volumeMeasure g) (𝓝[>] 0) (𝓝 0)

lemma ConservativeHeatKernelData.heat_operator_eq_laplacian
    {g : RiemannianMetric n M} (H : ConservativeHeatKernelData g)
    (x y : M) {t : ℝ} (ht : 0 < t) :
    deriv (fun s => H.kernel x y s) t =
      H.connection.laplacian (fun z => H.kernel z y t) x :=
  H.heat_equation x y t ht

lemma ConservativeHeatKernelData.first_moment_iSup_le
    {g : RiemannianMetric n M} (H : ConservativeHeatKernelData g)
    {C : ℝ} (hC : 0 < C ∧
      ∀ x t, 0 < t → t ≤ 1 →
        ∫ y, (g.edist x y).toReal * H.kernel x y t ∂volumeMeasure g ≤ C)
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    (⨆ x, ∫ y, (g.edist x y).toReal * H.kernel x y t
      ∂volumeMeasure g) ≤ C := by
  exact Real.iSup_le (fun x ↦ hC.2 x t ht ht1) hC.1.le

lemma ConservativeHeatKernelData.exists_first_moment_iSup_bound
    {g : RiemannianMetric n M} (H : ConservativeHeatKernelData g) :
    ∃ C : ℝ, 0 < C ∧
      ∀ t, 0 < t → t ≤ 1 →
        (⨆ x, ∫ y, (g.edist x y).toReal * H.kernel x y t
          ∂volumeMeasure g) ≤ C := by
  rcases H.first_moment_bound with ⟨C, hC, hbound⟩
  refine ⟨C, hC, fun t ht ht1 ↦ ?_⟩
  exact H.first_moment_iSup_le ⟨hC, hbound⟩ ht ht1

end PoincareConjecture.RiemannianMetric
