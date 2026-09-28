import PoincareConjecture.Proofs.M34.Mathlib.FiniteCoordinateEnergyRegularity
import PoincareConjecture.Proofs.M34.Standard.CanonicalDifferenceRegularity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set MeasureTheory
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.M34

open DifferenceEnergy

variable {n dH dA dS : ℕ} (U : Set (V n)) (hU : IsOpen U) [Nonempty U]
  (qH : FH n ≃L[ℝ] EuclideanSpace ℝ (Fin dH))
  (qA : FA n ≃L[ℝ] EuclideanSpace ℝ (Fin dA))
  (qS : FS n ≃L[ℝ] EuclideanSpace ℝ (Fin dS))
  {φ : V n → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
  (hφU : tsupport φ ⊆ U)

include hφ hφc hφU

theorem canonicalDomain_hasDerivAt_difference_energy :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    letI : MeasurableSpace (V n) := borel _
    letI : BorelSpace (V n) := ⟨rfl⟩
    ∀ {J J' : Set ℝ} (F : RicciFlow n U J) (F' : RicciFlow n U J')
      (R R' : ℝ → U → FS n),
      (∀ t x u v w, R t x u v w = (F.connection t).curvature x u v w) →
      (∀ t x u v w, R' t x u v w = (F'.connection t).curvature x u v w) →
      ∀ p : U,
        let r := (extChartAt (𝓡 n) p).symm
        let H : ℝ × V n → FH n := fun z =>
          (F.metric z.1).inner (r z.2) - (F'.metric z.1).inner (r z.2)
        let A : ℝ × V n → FA n := fun z => CovariantDerivative.difference
          (F.connection z.1).connection (F'.connection z.1).connection (r z.2)
        let S := fun z : ℝ × V n => R z.1 (r z.2) - R' z.1 (r z.2)
        ∀ t ∈ interior (J ∩ J'),
          HasDerivAt (fun s =>
            (∑ i, ∫ x, (φ x * qH (H (s, x)) i) ^ 2) +
            (∑ i, ∫ x, (φ x * qA (A (s, x)) i) ^ 2) +
            (∑ i, ∫ x, (φ x * qS (S (s, x)) i) ^ 2))
            ((∑ i, ∫ x, 2 * φ x ^ 2 * qH (H (t, x)) i *
              fderiv ℝ (fun z => qH (H z) i) (t, x) (1, 0)) +
            (∑ i, ∫ x, 2 * φ x ^ 2 * qA (A (t, x)) i *
              fderiv ℝ (fun z => qA (A z) i) (t, x) (1, 0)) +
            (∑ i, ∫ x, 2 * φ x ^ 2 * qS (S (t, x)) i *
              fderiv ℝ (fun z => qS (S z) i) (t, x) (1, 0))) t := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  let : MeasurableSpace (V n) := borel _
  let : BorelSpace (V n) := ⟨rfl⟩
  intro J J' F F' R R' hR hR' p r H A S t ht
  obtain ⟨hsH, hsA, hsS⟩ := canonicalDomain_contDiffOn_difference_coordinates U hU
    qH qA qS F F' R R' hR hR' p
  have hd {d : ℕ} (C : ℝ × V n → EuclideanSpace ℝ (Fin d))
      (hC : ContDiffOn ℝ ∞ C ((J ∩ J') ×ˢ U)) :
      HasDerivAt (fun s => ∑ i, ∫ x, (φ x * C (s, x) i) ^ 2)
        (∑ i, ∫ x, 2 * φ x ^ 2 * C (t, x) i *
          fderiv ℝ (fun z => C z i) (t, x) (1, 0)) t := by
    exact hasDerivAt_finite_coordinate_energy isOpen_interior hU
      ((hC.mono (Set.prod_mono interior_subset subset_rfl)).of_le (by decide)) hφ hφc hφU ht
  exact ((hd _ hsH).add (hd _ hsA)).add (hd _ hsS)

theorem canonicalDomain_continuousOn_difference_energy :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    letI : MeasurableSpace (V n) := borel _
    letI : BorelSpace (V n) := ⟨rfl⟩
    ∀ {J J' : Set ℝ} (F : RicciFlow n U J) (F' : RicciFlow n U J')
      (R R' : ℝ → U → FS n),
      (∀ t x u v w, R t x u v w = (F.connection t).curvature x u v w) →
      (∀ t x u v w, R' t x u v w = (F'.connection t).curvature x u v w) →
      ∀ p : U,
        let r := (extChartAt (𝓡 n) p).symm
        let H : ℝ × V n → FH n := fun z =>
          (F.metric z.1).inner (r z.2) - (F'.metric z.1).inner (r z.2)
        let A : ℝ × V n → FA n := fun z => CovariantDerivative.difference
          (F.connection z.1).connection (F'.connection z.1).connection (r z.2)
        let S := fun z : ℝ × V n => R z.1 (r z.2) - R' z.1 (r z.2)
        ∀ K : Set ℝ, IsCompact K → K ⊆ J ∩ J' →
          ContinuousOn (fun s =>
            (∑ i, ∫ x, (φ x * qH (H (s, x)) i) ^ 2) +
            (∑ i, ∫ x, (φ x * qA (A (s, x)) i) ^ 2) +
            (∑ i, ∫ x, (φ x * qS (S (s, x)) i) ^ 2)) K := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  let : MeasurableSpace (V n) := borel _
  let : BorelSpace (V n) := ⟨rfl⟩
  intro J J' F F' R R' hR hR' p r H A S K hK hKJ
  obtain ⟨hsH, hsA, hsS⟩ := canonicalDomain_contDiffOn_difference_coordinates U hU
    qH qA qS F F' R R' hR hR' p
  have hc {d : ℕ} (C : ℝ × V n → EuclideanSpace ℝ (Fin d))
      (hC : ContDiffOn ℝ ∞ C ((J ∩ J') ×ˢ U)) :
      ContinuousOn (fun s => ∑ i, ∫ x, (φ x * C (s, x) i) ^ 2) K := by
    exact continuousOn_finite_coordinate_energy hK hU
      (hC.continuousOn.mono (Set.prod_mono hKJ subset_rfl)) hφ hφc hφU
  intro s hs
  exact ((hc _ hsH s hs).add (hc _ hsA s hs)).add (hc _ hsS s hs)

end PoincareConjecture.M34
