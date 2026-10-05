import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Energy.CanonicalEnergyBound
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Energy.CanonicalEnergyRate

/-!
# Uniform actual energies for a family of pairs of flows

Two uniform positive ellipticity constants and spatial three-jet bounds
give uniform values and one-sided rates of the actual local energies.
The constants are chosen before the family index and tested time. This
is Morgan-Tian Section 12.5, pp. 309-319 and
uniqueness-assembly-interfaces.md.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
-- Actual curvature takes values in three nested Hom spaces.
set_option maxSynthPendingDepth 8

open Set MeasureTheory
open scoped Manifold ContDiff

namespace PoincareMT.M34

open DifferenceEnergy

/-- Uniform elliptic three-jets give one value bound and one local
support-rate constant for a whole family (Section 12.5, pp. 309-319). -/
theorem exists_uniformFamily_energy_bounds
    {n dH dA dS : ℕ} (U : Set (V n)) (hU : IsOpen U) [Nonempty U]
    (qH : FH n ≃L[ℝ] EuclideanSpace ℝ (Fin dH))
    (qA : FA n ≃L[ℝ] EuclideanSpace ℝ (Fin dA))
    (qS : FS n ≃L[ℝ] EuclideanSpace ℝ (Fin dS))
    {φ : V n → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) {a₀ a₁ : ℝ} (ha₀ : 0 < a₀) (ha₁ : 0 < a₁)
    (M₀ M₁ : ℝ) :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    letI : MeasurableSpace (V n) := borel _
    letI : BorelSpace (V n) := ⟨rfl⟩
    ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧ ∀ {ι : Type*} {J J' K : Set ℝ}
      (F : ι → RicciFlow n U J) (F' : ι → RicciFlow n U J') (p : U),
      (∀ i t, t ∈ K → ∀ x ∈ tsupport φ,
        let A := ((F i).metric t).pullbackCoefficients (extChartAt (𝓡 n) p).symm
        (∀ j ≤ 3, ‖iteratedFDeriv ℝ j A x‖ ≤ M₀) ∧
          ∀ v, a₀ * ‖v‖ ^ 2 ≤ A x v v) →
      (∀ i t, t ∈ K → ∀ x ∈ tsupport φ,
        let A := ((F' i).metric t).pullbackCoefficients (extChartAt (𝓡 n) p).symm
        (∀ j ≤ 3, ‖iteratedFDeriv ℝ j A x‖ ≤ M₁) ∧
          ∀ v, a₁ * ‖v‖ ^ 2 ≤ A x v v) →
      (∀ i t, t ∈ K → t ∈ J ∩ J' →
        canonicalDifferenceEnergy U hU qH qA qS φ (F i) (F' i) p t ≤ B) ∧
      (∀ i t, t ∈ K → t ∈ interior (J ∩ J') →
        deriv (canonicalDifferenceEnergy U hU qH qA qS φ (F i) (F' i) p) t ≤
          C * ∫ x in tsupport φ,
            canonicalDifferenceDensity U hU qH qA qS (F i) (F' i) p t x) := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  let : MeasurableSpace (V n) := borel _
  let : BorelSpace (V n) := ⟨rfl⟩
  have ha : 0 < min a₀ a₁ := lt_min ha₀ ha₁
  obtain ⟨B, hB, hb⟩ := exists_canonicalDifferenceEnergy_bound U hU qH qA qS
    hφ.continuous hφc hφU ha (max M₀ M₁)
  obtain ⟨C, hC, hc⟩ := exists_canonicalDifferenceEnergy_rate_bound U hU qH qA qS
    hφ hφc hφU ha (max M₀ M₁)
  refine ⟨B, C, hB, hC, ?_⟩
  intro ι J J' K F F' p h₀ h₁
  have hj₀ (i) (t) (ht : t ∈ K) (x) (hx : x ∈ tsupport φ) (j) (hj : j ≤ 3) :=
    ((h₀ i t ht x hx).1 j hj).trans (le_max_left M₀ M₁)
  have hj₁ (i) (t) (ht : t ∈ K) (x) (hx : x ∈ tsupport φ) (j) (hj : j ≤ 3) :=
    ((h₁ i t ht x hx).1 j hj).trans (le_max_right M₀ M₁)
  have he₀ (i) (t) (ht : t ∈ K) (x) (hx : x ∈ tsupport φ) (v : V n) :=
    (mul_le_mul_of_nonneg_right (min_le_left a₀ a₁) (sq_nonneg ‖v‖)).trans
      ((h₀ i t ht x hx).2 v)
  have he₁ (i) (t) (ht : t ∈ K) (x) (hx : x ∈ tsupport φ) (v : V n) :=
    (mul_le_mul_of_nonneg_right (min_le_right a₀ a₁) (sq_nonneg ‖v‖)).trans
      ((h₁ i t ht x hx).2 v)
  exact ⟨fun i t ht htJ => hb (F i) (F' i) p htJ
      (hj₀ i t ht) (hj₁ i t ht) (he₀ i t ht) (he₁ i t ht),
    fun i t ht htJ => hc (F i) (F' i) p htJ
      (hj₀ i t ht) (hj₁ i t ht) (he₀ i t ht) (he₁ i t ht)⟩

end PoincareMT.M34
