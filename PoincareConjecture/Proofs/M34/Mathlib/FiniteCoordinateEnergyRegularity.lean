import PoincareConjecture.Proofs.M03.LocalCoordinateEnergy










set_option autoImplicit false

open Set MeasureTheory
open scoped ContDiff Topology BigOperators

namespace PoincareConjecture.M34



theorem hasDerivAt_finite_coordinate_energy
    {n : ℕ} {ι : Type*} [Fintype ι] {I : Set ℝ} (hI : IsOpen I)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {F : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ ι}
    (hF : ContDiffOn ℝ 1 F (I ×ˢ U))
    {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U)
    {t : ℝ} (ht : t ∈ I) :
    letI : MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _
    letI : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
    HasDerivAt (fun s => ∑ i, ∫ x, (φ x * F (s, x) i) ^ 2)
      (∑ i, ∫ x, 2 * φ x ^ 2 * F (t, x) i *
        fderiv ℝ (fun z => F z i) (t, x) (1, 0)) t := by
  let : MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _
  let : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
  apply HasDerivAt.fun_sum
  intro i _
  have hi : ContDiffOn ℝ 1 (fun z => F z i) (I ×ˢ U) :=
    (EuclideanSpace.proj i : EuclideanSpace ℝ ι →L[ℝ] ℝ).contDiff.comp_contDiffOn hF
  exact Proofs.M03.hasDerivAt_local_coordinate_energy hI hU hi hφ hφc hφU ht



theorem continuousOn_finite_coordinate_energy
    {n : ℕ} {ι : Type*} [Fintype ι] {K : Set ℝ} (hK : IsCompact K)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {F : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ ι}
    (hF : ContinuousOn F (K ×ˢ U))
    {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) :
    letI : MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _
    letI : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
    ContinuousOn (fun s => ∑ i, ∫ x, (φ x * F (s, x) i) ^ 2) K := by
  let : MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _
  let : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
  apply continuousOn_finsetSum
  intro i _
  have hi : ContinuousOn (fun z => F z i) (K ×ˢ U) :=
    (EuclideanSpace.proj i : EuclideanSpace ℝ ι →L[ℝ] ℝ).continuous.comp_continuousOn hF
  exact Proofs.M03.continuousOn_local_coordinate_energy hK hU hi hφ hφc hφU

end PoincareConjecture.M34
