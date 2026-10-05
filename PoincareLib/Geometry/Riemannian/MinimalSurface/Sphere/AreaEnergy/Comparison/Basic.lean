import PoincareLib.Geometry.Riemannian.MinimalSurface.Sphere.Uniformization.Basic
import PoincareLib.Geometry.Riemannian.MinimalSurface.Sphere.AreaEnergy.Comparison.C1

/-!
# Area-to-energy conversion for C1 spheres

Global uniformization and smooth majorants of the pullback metric
identify the area and energy infima in the non-null C1 class.
Source: Morgan-Tian Lemma 18.10, printed pp. 424-426, with the corrected
area-to-energy step recorded in the M60 derivation.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

noncomputable section

namespace PoincareMT
/-- Area-to-energy approximation for every C1 sphere, preserving non-nullness.
Source: MT Lemma 18.10, pp. 424-426, corrected area-to-energy step. -/
theorem m60SphereAreaToEnergy {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (f : UnitTwoSphere → M)
    (hf : ContMDiff (𝓡 2) (𝓡 n) 1 f) (eta : ℝ) (heta : 0 < eta) :
    ∃ h : UnitTwoSphere → M, ContMDiff (𝓡 2) (𝓡 n) 1 h ∧
      m60SphereEnergy g h < m60SphereArea g f + eta ∧
      (IsNullHomotopicSphere h → IsNullHomotopicSphere f) :=
  m60SphereAreaToEnergy_of_uniformization M60.sphere_uniformization g f hf eta heta

/-- Area and energy have the same infimum over all non-null C1 spheres.
Source: MT Lemma 18.10, pp. 424-426, corrected area-to-energy step. -/
theorem m60SphereArea_energy_infimum {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) :
    sInf (m60SphereArea g '' {f | ContMDiff (𝓡 2) (𝓡 n) 1 f ∧
      ¬ IsNullHomotopicSphere f}) =
    sInf (m60SphereEnergy g '' {f | ContMDiff (𝓡 2) (𝓡 n) 1 f ∧
      ¬ IsNullHomotopicSphere f}) := by
  let S : Set (UnitTwoSphere → M) :=
    {f | ContMDiff (𝓡 2) (𝓡 n) 1 f ∧ ¬ IsNullHomotopicSphere f}
  change sInf (m60SphereArea g '' S) = sInf (m60SphereEnergy g '' S)
  have hA : BddBelow (m60SphereArea g '' S) := ⟨0, by
    rintro _ ⟨f, -, rfl⟩; exact m60SphereArea_nonneg g f⟩
  have hE : BddBelow (m60SphereEnergy g '' S) := ⟨0, by
    rintro _ ⟨f, -, rfl⟩; exact m60SphereEnergy_nonneg g f⟩
  by_cases hS : S.Nonempty
  · apply le_antisymm
    · refine le_csInf (hS.image _) ?_
      rintro _ ⟨f, hf, rfl⟩
      exact (csInf_le hA ⟨f, hf, rfl⟩).trans
        (m60SphereArea_le_energy_of_integrable g f (m60SphereEnergyDensity_integrable g f hf.1))
    · refine le_csInf (hS.image _) ?_
      rintro _ ⟨f, hf, rfl⟩
      by_contra hn
      obtain ⟨h, hh, he, hnul⟩ := m60SphereAreaToEnergy g f hf.1
        (sInf (m60SphereEnergy g '' S) - m60SphereArea g f) (sub_pos.mpr (lt_of_not_ge hn))
      have hb := csInf_le hE ⟨h, ⟨hh, fun hnull => hf.2 (hnul hnull)⟩, rfl⟩
      linarith
  · rw [Set.not_nonempty_iff_eq_empty.mp hS]
    simp
end PoincareMT
end
