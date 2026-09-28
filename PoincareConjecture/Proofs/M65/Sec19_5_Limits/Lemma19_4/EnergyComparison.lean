import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.ConformalVariation
import PoincareConjecture.Proofs.M58.Mathlib.TwoVectorArea

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem m65AreaDensity_le_energyDensity (g : RiemannianMetric n M)
    (f : LoopPlane → M) (z : LoopPlane) :
    m60AreaDensity g f z ≤ m60EnergyDensity g f z := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let x := mfderiv (𝓡 2) (𝓡 n) f z (EuclideanSpace.basisFun (Fin 2) ℝ 0)
  let y := mfderiv (𝓡 2) (𝓡 n) f z (EuclideanSpace.basisFun (Fin 2) ℝ 1)
  have hdet : (m60AreaGram g f z).det =
      inner ℝ x x * inner ℝ y y - (inner ℝ x y) ^ 2 := by
    rw [Matrix.det_fin_two]
    change inner ℝ x x * inner ℝ y y - inner ℝ x y * inner ℝ y x = _
    rw [real_inner_comm x y]
    ring
  have harea : m60AreaDensity g f z = Proofs.M58.twoVectorArea x y := by
    simp only [m60AreaDensity, hdet, Proofs.M58.twoVectorArea]
  have henergy : m60EnergyDensity g f z = (‖x‖ ^ 2 + ‖y‖ ^ 2) / 2 := by
    simp only [m60EnergyDensity, Matrix.trace, Fin.sum_univ_two]
    change (1 / 2 : ℝ) * (inner ℝ x x + inner ℝ y y) = _
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    ring
  rw [harea, henergy]
  exact (Proofs.M58.twoVectorArea_le x y).trans (by nlinarith [sq_nonneg (‖x‖ - ‖y‖)])

theorem m65AreaDensity_eq_energyDensity_of_conformal (g : RiemannianMetric n M)
    (f : LoopPlane → M) (z : LoopPlane) (c : ℝ)
    (hconf : m60AreaGram g f z = c • (1 : Matrix (Fin 2) (Fin 2) ℝ)) :
    m60AreaDensity g f z = m60EnergyDensity g f z := by
  rw [m65AreaDensity_eq_of_conformal g f z c hconf, m60EnergyDensity, hconf,
    Matrix.trace_smul, Matrix.trace_one]
  simp only [Fintype.card_fin, Nat.cast_ofNat, smul_eq_mul]
  ring

end PoincareConjecture

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

theorem m65ParametrizedArea_le_energy (g : RiemannianMetric 3 M) (f : LoopPlane → M)
    (harea : IntegrableOn (parametrizedAreaDensity g f) loopDiskSet volume)
    (henergy : IntegrableOn (m60EnergyDensity g f) loopDiskSet volume) :
    parametrizedRiemannianArea g f ≤ ∫ z in loopDiskSet, m60EnergyDensity g f z := by
  exact integral_mono harea henergy (m65AreaDensity_le_energyDensity g f)

theorem m65ParametrizedArea_eq_energy_of_conformal
    (g : RiemannianMetric 3 M) (f : LoopPlane → M)
    (hconf : ∀ᵐ z ∂volume.restrict loopDiskSet,
      ∃ c : ℝ, m60AreaGram g f z = c • (1 : Matrix (Fin 2) (Fin 2) ℝ)) :
    parametrizedRiemannianArea g f = ∫ z in loopDiskSet, m60EnergyDensity g f z := by
  apply integral_congr_ae
  filter_upwards [hconf] with z hz
  obtain ⟨c, hc⟩ := hz
  exact m65AreaDensity_eq_energyDensity_of_conformal g f z c hc

end PoincareConjecture
