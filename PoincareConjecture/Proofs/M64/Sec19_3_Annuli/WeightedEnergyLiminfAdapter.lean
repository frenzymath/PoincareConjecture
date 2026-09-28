import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.EnergyAttainment
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.WeakDirichletLowerSemicontinuity














set_option autoImplicit false

open Set Filter MeasureTheory
open Poincare.Analysis.Sobolev.Weak
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {c0 c1 : ℝ → M}






structure M64WeightedColumnLiminfInput
    {S : M64AnnulusMinimizingSequenceCertificate
      (g := g) (c0 := c0) (c1 := c1)}
    {C : M64CourantLebesgueArzelaCertificate S}
    (A : M64Annulus g c0 c1) where
  map_eq_limit : A.map = C.limit.map
  classical_energy_integrable : IntegrableOn (m60EnergyDensity g A.map)
    m64AnnulusDomain volume
  column_limit : Fin 2 → Lp (EuclideanSpace ℝ (Fin n)) 2
    (volume.restrict m64AnnulusDomain)
  column_sequence : Fin 2 → ℕ → Lp (EuclideanSpace ℝ (Fin n)) 2
    (volume.restrict m64AnnulusDomain)
  column_weak : ∀ i : Fin 2,
    Poincare.Analysis.Sobolev.WeakCompactness.WeakConverges
      (column_sequence i) (column_limit i)
  column_bound : Fin 2 → ℝ
  column_bound_spec : ∀ i : Fin 2, ∀ k : ℕ,
    ‖column_sequence i k‖ ^ 2 ≤ column_bound i
  sequence_energy_identification : ∀ k : ℕ,
    (∫ p in m64AnnulusDomain,
      m60EnergyDensity g (S.sequence (C.subsequence k)).map p) =
      (‖column_sequence 0 k‖ ^ 2 + ‖column_sequence 1 k‖ ^ 2) / 2
  classical_weak_energy_identification :
    (∫ p in m64AnnulusDomain,
      m60EnergyDensity g A.map p) =
      ∫ p in m64AnnulusDomain,
        m64AnnulusWeakEnergyDensity g C.limit.gradient p
  limit_energy_identification :
    (∫ p in m64AnnulusDomain,
      m64AnnulusWeakEnergyDensity g C.limit.gradient p) =
      (‖column_limit 0‖ ^ 2 + ‖column_limit 1‖ ^ 2) / 2





theorem M64WeightedColumnLiminfInput.toWeakEnergyCertificate
    {S : M64AnnulusMinimizingSequenceCertificate
      (g := g) (c0 := c0) (c1 := c1)}
    {C : M64CourantLebesgueArzelaCertificate S}
    {A : M64Annulus g c0 c1}
    (I : M64WeightedColumnLiminfInput (g := g) (c0 := c0) (c1 := c1)
      (S := S) (C := C) A) :
    M64WeakEnergyLowerSemicontinuityCertificate S C A := by
  refine {
    map_eq_limit := I.map_eq_limit
    classical_energy_integrable := I.classical_energy_integrable
    energy_identification := I.classical_weak_energy_identification
    weak_energy_le_liminf := ?_ }
  exact m64_integral_energy_le_liminf_of_weighted_columns
    (I.column_weak 0) (I.column_weak 1)
    (I.column_bound_spec 0) (I.column_bound_spec 1)
    I.sequence_energy_identification I.limit_energy_identification

end PoincareConjecture
