import PoincareConjecture.Proofs.M34.Mathlib.CutoffFiniteSquareIntegral
import PoincareConjecture.Proofs.M34.Standard.CanonicalDifferenceDensity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set MeasureTheory
open scoped Manifold ContDiff BigOperators

namespace PoincareConjecture.M34

open DifferenceEnergy

variable {n dH dA dS : ℕ} (U : Set (V n)) (hU : IsOpen U) [Nonempty U]
  (qH : FH n ≃L[ℝ] EuclideanSpace ℝ (Fin dH))
  (qA : FA n ≃L[ℝ] EuclideanSpace ℝ (Fin dA))
  (qS : FS n ≃L[ℝ] EuclideanSpace ℝ (Fin dS))
  {φ : V n → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
  (hφU : tsupport φ ⊆ U)

include hφ hφc hφU

theorem canonicalDifferenceDensity_integrable_cutoff :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    letI : MeasurableSpace (V n) := borel _
    letI : BorelSpace (V n) := ⟨rfl⟩
    ∀ {J J' : Set ℝ} (F : RicciFlow n U J) (F' : RicciFlow n U J') (p : U)
      {t : ℝ}, t ∈ J ∩ J' → Integrable (fun x : V n => φ x ^ 2 *
        canonicalDifferenceDensity U hU qH qA qS F F' p t x) (volume : Measure (V n)) := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  let : MeasurableSpace (V n) := borel _
  let : BorelSpace (V n) := ⟨rfl⟩
  intro J J' F F' p t ht
  have hwc : HasCompactSupport (fun x => φ x ^ 2) :=
    hφc.comp_left (g := fun r : ℝ => r ^ 2) (by simp)
  have hwU : tsupport (fun x => φ x ^ 2) ⊆ U := by
    simpa only [pow_two] using (tsupport_mul_subset_left (f := φ) (g := φ)).trans hφU
  exact integrable_cutoff_mul (μ := volume) hU (hφ.pow 2).continuousOn hwc hwU
    (canonicalDifferenceDensity_continuousOn_slice U hU qH qA qS F F' p ht)

theorem canonicalDifferenceDensity_integral_eq :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    letI : MeasurableSpace (V n) := borel _
    letI : BorelSpace (V n) := ⟨rfl⟩
    ∀ {J J' : Set ℝ} (F : RicciFlow n U J) (F' : RicciFlow n U J') (p : U)
      {t : ℝ}, t ∈ J ∩ J' →
      let r := (extChartAt (𝓡 n) p).symm
      let H : V n → FH n := fun x => (F.metric t).inner (r x) - (F'.metric t).inner (r x)
      let A : V n → FA n := fun x => CovariantDerivative.difference
        (F.connection t).connection (F'.connection t).connection (r x)
      let S : V n → FS n := fun x => curvatureTrilinearMap (F.connection t) (r x) -
        curvatureTrilinearMap (F'.connection t) (r x)
      (∫ x, φ x ^ 2 * canonicalDifferenceDensity U hU qH qA qS F F' p t x) =
        (∑ i, ∫ x, (φ x * qH (H x) i) ^ 2) +
        (∑ i, ∫ x, (φ x * qA (A x) i) ^ 2) +
        (∑ i, ∫ x, (φ x * qS (S x) i) ^ 2) := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  let : MeasurableSpace (V n) := borel _
  let : BorelSpace (V n) := ⟨rfl⟩
  intro J J' F F' p t ht r H A S
  obtain ⟨hH, hA, hS⟩ := canonicalDomain_contDiffOn_difference_coordinates U hU qH qA qS
    F F' (fun s x => curvatureTrilinearMap (F.connection s) x)
    (fun s x => curvatureTrilinearMap (F'.connection s) x)
    (fun s x u v w => curvatureTrilinearMap_apply (F.connection s) x u v w)
    (fun s x u v w => curvatureTrilinearMap_apply (F'.connection s) x u v w) p
  have hslice : ContinuousOn (fun x : V n => (t, x)) U :=
    (continuous_const.prodMk continuous_id).continuousOn
  have hmap : MapsTo (fun x : V n => (t, x)) U ((J ∩ J') ×ˢ U) := fun _ hx => ⟨ht, hx⟩
  have hcH : ContinuousOn (fun x => qH (H x)) U := by
    intro x hx
    exact (hH.continuousOn (t, x) ⟨ht, hx⟩).comp (hslice x hx) hmap
  have hcA : ContinuousOn (fun x => qA (A x)) U := by
    intro x hx
    exact (hA.continuousOn (t, x) ⟨ht, hx⟩).comp (hslice x hx) hmap
  have hcS : ContinuousOn (fun x => qS (S x)) U := by
    intro x hx
    exact (hS.continuousOn (t, x) ⟨ht, hx⟩).comp (hslice x hx) hmap
  have hwc : HasCompactSupport (fun x => φ x ^ 2) :=
    hφc.comp_left (g := fun r : ℝ => r ^ 2) (by simp)
  have hwU : tsupport (fun x => φ x ^ 2) ⊆ U := by
    simpa only [pow_two] using (tsupport_mul_subset_left (f := φ) (g := φ)).trans hφU
  have hi {d : ℕ} (f : V n → EuclideanSpace ℝ (Fin d)) (hf : ContinuousOn f U) :
      Integrable (fun x : V n => φ x ^ 2 * ∑ i, f x i ^ 2) (volume : Measure (V n)) := by
    apply integrable_cutoff_mul (μ := volume) hU (hφ.pow 2).continuousOn hwc hwU
    exact continuousOn_finsetSum _ (fun i _ =>
      ((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).continuous.comp_continuousOn
        hf).pow 2)
  have he {d : ℕ} (f : V n → EuclideanSpace ℝ (Fin d)) (hf : ContinuousOn f U) :
      (∫ x, φ x ^ 2 * ∑ i, f x i ^ 2) = ∑ i, ∫ x, (φ x * f x i) ^ 2 :=
    integral_cutoff_sq_finsetSum Finset.univ hU hφ.continuousOn hφc hφU (fun i _ =>
      (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).continuous.comp_continuousOn hf)
  change (∫ x, φ x ^ 2 * ((∑ i, qH (H x) i ^ 2) +
    (∑ i, qA (A x) i ^ 2) + (∑ i, qS (S x) i ^ 2))) = _
  simp_rw [mul_add]
  have hadd := integral_add ((hi _ hcH).add (hi _ hcA)) (hi _ hcS)
  simp only [Pi.add_apply] at hadd
  rw [hadd,
    integral_add (hi _ hcH) (hi _ hcA), he _ hcH, he _ hcA, he _ hcS]

end PoincareConjecture.M34
