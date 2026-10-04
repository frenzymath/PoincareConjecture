import PoincareLib.Geometry.CurveShortening.Deformation.Plateau.Weak.MinimizerEnergyNormalization
import PoincareLib.Geometry.CurveShortening.Deformation.Plateau.Energy.Competitors

/-!
# Genuine normalized energy competitors

The constructed epsilon-conformal filling and actual conformal
normalization discharge the energy comparison in the normalized weak
Plateau class. Source: Morrey ICM 1950, pp. 181-185, for Morgan--Tian
Lemma 19.2, printed pp. 437-438; M65 derivations 30 and 32.
-/

set_option autoImplicit false

open Set MeasureTheory Complex
open scoped Manifold ContDiff

universe u

namespace PoincareMT

/-- Actual energy comparison and actual normalization give a genuine
three-point pinned filling, with no energy-competitor premise.
Source: Morrey ICM pp. 181-185, MT Lemma 19.2, pp. 437-438;
M65 derivations 30 and 32. -/
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

end PoincareMT
