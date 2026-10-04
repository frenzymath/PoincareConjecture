import PoincareLib.Geometry.RicciFlow.Local.Energy.Coordinates.LocalCoordinateEnergy
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Local.Energy.Coordinates.LocalCoordinateEnergy

/-!
# Pointwise detection by finite-coordinate energy

Every coordinate energy is nonnegative. A vanishing finite sum therefore
annihilates each scalar energy, and local continuity detects the vector
field wherever the compact cutoff is nonzero. This is Morgan-Tian
Section 12.5, pp. 309-319 and finite-energy-zero.md.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped Topology BigOperators

namespace PoincareMT.M34

/-- Finite-coordinate energy vanishes exactly when the continuous vector
field vanishes on the nonzero-cutoff region (Section 12.5, pp. 309-319). -/
theorem finite_coordinate_energy_eq_zero_iff
    {n : ℕ} {ι : Type*} [Fintype ι]
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ ι} (hF : ContinuousOn F U)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) :
    letI : MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _
    letI : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
    (∑ i, ∫ x, (φ x * F x i) ^ 2) = 0 ↔ ∀ x, φ x ≠ 0 → F x = 0 := by
  let : MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _
  let : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
  classical
  have hc (i : ι) : ContinuousOn (fun x => F x i) U :=
    (EuclideanSpace.proj i : EuclideanSpace ℝ ι →L[ℝ] ℝ).continuous.comp_continuousOn hF
  have hn (i : ι) : 0 ≤ ∫ x, (φ x * F x i) ^ 2 :=
    integral_nonneg (fun x => sq_nonneg (φ x * F x i))
  constructor
  · intro hzero x hx
    ext i
    have hi : (∫ y, (φ y * F y i) ^ 2) = 0 :=
      le_antisymm
        ((Finset.single_le_sum (fun j _ => hn j) (Finset.mem_univ i)).trans_eq hzero) (hn i)
    have hz := (Proofs.M03.local_coordinate_energy_eq_zero_iff hU (hc i) hφ hφc hφU).mp hi x
    exact (mul_eq_zero.mp hz).resolve_left hx
  · intro hzero
    apply Finset.sum_eq_zero
    intro i _
    apply (Proofs.M03.local_coordinate_energy_eq_zero_iff hU (hc i) hφ hφc hφU).mpr
    intro x
    by_cases hx : φ x = 0
    · simp only [hx, zero_mul]
    · simp [hzero x hx]

end PoincareMT.M34
