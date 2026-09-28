import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerEnergyNormalization
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.EnergyCompetitors










set_option autoImplicit false

open Set MeasureTheory Complex
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture





theorem m65SpanningDisk_exists_normalized_energy_competitor
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} {γ : C1FreeLoopSpace (M := M)}
    (a b c : LoopCircle) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (D : LipschitzSpanningDisk g γ) (ε : ℝ) (hε : 0 < ε) :
    ∃ D' : LipschitzSpanningDisk g γ, D'.area = D.area ∧
      IntegrableOn (m60EnergyDensity g D'.map) loopDiskSet volume ∧
      (∫ z in loopDiskSet, m60EnergyDensity g D'.map z) ≤ D.area + ε ∧
      (D'.reparameterization.inverse a).val = orthonormalBasisOneI.repr 1 ∧
      (D'.reparameterization.inverse b).val = orthonormalBasisOneI.repr (-1) ∧
      ((D'.reparameterization.inverse c).val = orthonormalBasisOneI.repr I ∨
        (D'.reparameterization.inverse c).val = orthonormalBasisOneI.repr (-I)) := by
  apply m65SpanningDisk_normalizedEnergyComparison ?_ a b c hab hac hbc D ε hε
  intro F η hη
  obtain ⟨F', harea, hi, hE⟩ := m65SpanningDisk_exists_energy_competitor F hη
  exact ⟨F', harea, hi, hE.le⟩

end PoincareConjecture
