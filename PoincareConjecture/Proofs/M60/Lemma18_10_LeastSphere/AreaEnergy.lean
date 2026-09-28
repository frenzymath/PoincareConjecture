import PoincareConjecture.Definitions.M60Area
import Mathlib.Analysis.InnerProductSpace.Basic

set_option autoImplicit false

open MeasureTheory
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem m60AreaGram_symm (g : RiemannianMetric n M)
    (f : LoopPlane → M) (z : LoopPlane) (i j : Fin 2) :
    m60AreaGram g f z i j = m60AreaGram g f z j i :=
  g.symm _ _ _

theorem m60AreaGram_diagonal_nonneg (g : RiemannianMetric n M)
    (f : LoopPlane → M) (z : LoopPlane) (i : Fin 2) :
    0 ≤ m60AreaGram g f z i i := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact real_inner_self_nonneg
    (x := mfderiv (𝓡 2) (𝓡 n) f z (EuclideanSpace.basisFun (Fin 2) ℝ i))

theorem m60AreaGram_det_nonneg (g : RiemannianMetric n M)
    (f : LoopPlane → M) (z : LoopPlane) :
    0 ≤ Matrix.det (m60AreaGram g f z) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let d := mfderiv (𝓡 2) (𝓡 n) f z
  let v := fun i => d (EuclideanSpace.basisFun (Fin 2) ℝ i)
  rw [Matrix.det_fin_two, m60AreaGram_symm g f z 1 0]
  exact sub_nonneg.mpr (real_inner_mul_inner_self_le (v 0) (v 1))

theorem m60AreaDensity_nonneg (g : RiemannianMetric n M)
    (f : LoopPlane → M) (z : LoopPlane) : 0 ≤ m60AreaDensity g f z :=
  Real.sqrt_nonneg _

theorem m60EnergyDensity_nonneg (g : RiemannianMetric n M)
    (f : LoopPlane → M) (z : LoopPlane) : 0 ≤ m60EnergyDensity g f z := by
  unfold m60EnergyDensity
  rw [Matrix.trace_fin_two]
  exact mul_nonneg (by norm_num)
    (add_nonneg (m60AreaGram_diagonal_nonneg g f z 0)
      (m60AreaGram_diagonal_nonneg g f z 1))

theorem m60AreaDensity_le_energyDensity (g : RiemannianMetric n M)
    (f : LoopPlane → M) (z : LoopPlane) :
    m60AreaDensity g f z ≤ m60EnergyDensity g f z := by
  unfold m60AreaDensity
  apply Real.sqrt_le_iff.mpr
  refine ⟨m60EnergyDensity_nonneg g f z, ?_⟩
  rw [max_le_iff]
  refine ⟨sq_nonneg _, ?_⟩
  unfold m60EnergyDensity
  rw [Matrix.trace_fin_two, Matrix.det_fin_two, m60AreaGram_symm g f z 1 0]
  nlinarith [sq_nonneg (m60AreaGram g f z 0 0 - m60AreaGram g f z 1 1),
    sq_nonneg (m60AreaGram g f z 0 1)]

theorem m60AreaDensity_eq_energyDensity_of_gram (g : RiemannianMetric n M)
    (f : LoopPlane → M) (z : LoopPlane)
    (hequal : m60AreaGram g f z 0 0 = m60AreaGram g f z 1 1)
    (horthogonal : m60AreaGram g f z 0 1 = 0) :
    m60AreaDensity g f z = m60EnergyDensity g f z := by
  have hnonneg := m60AreaGram_diagonal_nonneg g f z 1
  unfold m60AreaDensity m60EnergyDensity
  rw [Matrix.det_fin_two, Matrix.trace_fin_two, horthogonal, zero_mul, sub_zero, hequal]
  rw [max_eq_right (mul_nonneg hnonneg hnonneg), Real.sqrt_mul_self hnonneg]
  ring

theorem m60SphereArea_nonneg (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) : 0 ≤ m60SphereArea g f :=
  integral_nonneg (m60AreaDensity_nonneg g (f ∘ m60SphereParameter))

theorem m60SphereEnergy_nonneg (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) : 0 ≤ m60SphereEnergy g f :=
  integral_nonneg (m60EnergyDensity_nonneg g (f ∘ m60SphereParameter))

theorem m60SphereArea_le_energy_of_integrable (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (henergy : Integrable (m60SphereEnergyDensity g f) volume) :
    m60SphereArea g f ≤ m60SphereEnergy g f :=
  integral_mono_of_nonneg
    (Filter.Eventually.of_forall (m60AreaDensity_nonneg g (f ∘ m60SphereParameter)))
    henergy
    (Filter.Eventually.of_forall (m60AreaDensity_le_energyDensity g (f ∘ m60SphereParameter)))

end PoincareConjecture
