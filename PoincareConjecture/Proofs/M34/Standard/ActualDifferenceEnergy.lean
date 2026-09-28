import PoincareConjecture.Proofs.M34.Mathlib.CutoffSquareIntegral
import PoincareConjecture.Proofs.M34.Standard.ActualConnectionIntegralEnergy
import PoincareConjecture.Proofs.M34.Standard.ActualCurvatureIntegralEnergy
import PoincareConjecture.Proofs.M34.Standard.CanonicalMetricEnergy
import PoincareConjecture.Proofs.M34.Standard.CanonicalDifferenceEnergyRegularity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set MeasureTheory
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.M34

open DifferenceEnergy

set_option maxHeartbeats 2400000 in

theorem exists_uniform_actual_difference_energy_bound
    {n dH dA dS : ℕ} (U : Set (V n)) (hU : IsOpen U) [Nonempty U]
    (qH : FH n ≃L[ℝ] EuclideanSpace ℝ (Fin dH))
    (qA : FA n ≃L[ℝ] EuclideanSpace ℝ (Fin dA))
    (qS : FS n ≃L[ℝ] EuclideanSpace ℝ (Fin dS))
    {φ : V n → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) {a : ℝ} (ha : 0 < a) (M : ℝ) :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    letI : MeasurableSpace (V n) := borel _
    letI : BorelSpace (V n) := ⟨rfl⟩
    ∃ lambda C : ℝ, 0 < lambda ∧ 0 ≤ C ∧
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
            let B0 := (F.metric t).pullbackCoefficients r
            let B1 := (F'.metric t).pullbackCoefficients r
            (∀ x ∈ tsupport φ, ∀ j ≤ 3, ‖iteratedFDeriv ℝ j B0 x‖ ≤ M) →
            (∀ x ∈ tsupport φ, ∀ j ≤ 3, ‖iteratedFDeriv ℝ j B1 x‖ ≤ M) →
            (∀ x ∈ tsupport φ, ∀ v, a * ‖v‖ ^ 2 ≤ B0 x v v) →
            (∀ x ∈ tsupport φ, ∀ v, a * ‖v‖ ^ 2 ≤ B1 x v v) →
            deriv (fun s => (∑ i, ∫ x, (φ x * qH (H (s, x)) i) ^ 2) +
              (∑ i, ∫ x, (φ x * qA (A (s, x)) i) ^ 2) +
              (∑ i, ∫ x, (φ x * qS (S (s, x)) i) ^ 2)) t ≤
              C * (∫ x in tsupport φ, (∑ i, qH (H (t, x)) i ^ 2) +
                (∑ i, qA (A (t, x)) i ^ 2) + (∑ i, qS (S (t, x)) i ^ 2)) -
                (lambda / 2) * (∑ alpha : Fin dS, ∫ x, φ x ^ 2 *
                  ∑ j : Fin n, (fderiv ℝ (fun y => qS (S (t, y)) alpha) x
                    (EuclideanSpace.single j 1)) ^ 2) := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  let : MeasurableSpace (V n) := borel _
  let : BorelSpace (V n) := ⟨rfl⟩
  classical
  obtain ⟨lambda, CS, hlambda, hCS, hcurvature⟩ :=
    exists_uniform_actual_curvature_integral_energy_bound U hU qH qA qS hφ hφc hφU ha M
  obtain ⟨CA, hCA, hconnection⟩ := exists_uniform_actual_connection_integral_energy_bound
    U hU qH qA qS hφ.continuous hφc hφU ha M
  obtain ⟨CH, hCH, hmetric⟩ := exists_canonicalDomain_metric_energy_bound U hU qH qS
  obtain ⟨B, hB, hcutoff⟩ := exists_integral_cutoff_sq_le_setIntegral
    (μ := volume) hU hφ.continuous hφc hφU
  let L := CA / (lambda / 8) + CA + 1 + CH
  have hL : 0 ≤ L := by dsimp [L]; positivity
  let C := CS + B * L
  refine ⟨lambda, C, hlambda, by dsimp [C]; positivity, ?_⟩
  intro J J' F F' R R' hR hR' p r H A S t ht B0 B1 hj0 hj1 he0 he1
  have hSr := hcurvature F F' R R' hR hR' p t ht hj0 hj1 he0 he1
  have hAr := hconnection F F' R R' hR hR' p t ht hj0 hj1 he0 he1
    (lambda / 8) (by positivity)
  have hHr := hmetric p φ hφ.continuous hφc hφU F F' R R' hR hR' t ht
  let rho := fun x => (∑ i, qH (H (t, x)) i ^ 2) +
    (∑ i, qA (A (t, x)) i ^ 2) + (∑ i, qS (S (t, x)) i ^ 2)
  let E := ∫ x, φ x ^ 2 * rho x
  let E0 := ∫ x in tsupport φ, rho x
  let D := ∑ alpha : Fin dS, ∫ x, φ x ^ 2 *
    ∑ j : Fin n, (fderiv ℝ (fun y => qS (S (t, y)) alpha) x (EuclideanSpace.single j 1)) ^ 2
  obtain ⟨hsH, hsA, hsS⟩ := canonicalDomain_contDiffOn_difference_coordinates U hU
    qH qA qS F F' R R' hR hR' p
  have hslice : ContinuousOn (fun x : V n => (t, x)) U :=
    (continuous_const.prodMk continuous_id).continuousOn
  have hmap : MapsTo (fun x : V n => (t, x)) U ((J ∩ J') ×ˢ U) :=
    fun _ hx => ⟨interior_subset ht, hx⟩
  have hcH : ContinuousOn (fun x => qH (H (t, x))) U := hsH.continuousOn.comp hslice hmap
  have hcA : ContinuousOn (fun x => qA (A (t, x))) U := hsA.continuousOn.comp hslice hmap
  have hcS : ContinuousOn (fun x => qS (S (t, x))) U := hsS.continuousOn.comp hslice hmap
  have hsq {d : ℕ} (f : V n → EuclideanSpace ℝ (Fin d)) (hf : ContinuousOn f U) :
      ContinuousOn (fun x => ∑ i, f x i ^ 2) U :=
    continuousOn_finsetSum _ (fun i _ =>
      ((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).continuous.comp_continuousOn
        hf).pow 2)
  have hrho : ContinuousOn rho U := ((hsq _ hcH).add (hsq _ hcA)).add (hsq _ hcS)
  have hE : E ≤ B * E0 := hcutoff rho hrho (fun x _ => by dsimp [rho]; positivity)
  have hwc : HasCompactSupport (fun x => φ x ^ 2) :=
    hφc.comp_left (g := fun r : ℝ => r ^ 2) (by simp)
  have hwφ : tsupport (fun x => φ x ^ 2) ⊆ tsupport φ := by
    simpa only [pow_two] using tsupport_mul_subset_left (f := φ) (g := φ)
  have hcomponent {d : ℕ} (f : V n → EuclideanSpace ℝ (Fin d))
      (hf : ContinuousOn f U) (hb : ∀ x ∈ tsupport φ, (∑ i, f x i ^ 2) ≤ rho x) :
      (∑ i, ∫ x, (φ x * f x i) ^ 2) ≤ E := by
    have hi := integral_cutoff_mul_finsetSum_le (μ := volume) (w := fun x => φ x ^ 2)
      (Finset.univ : Finset (Fin d))
      hU (hφ.continuous.pow 2).continuousOn hwc (hwφ.trans hφU)
      (fun x _ => sq_nonneg (φ x))
      (q := fun i x => f x i ^ 2) (g := rho)
      (fun i _ =>
        ((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).continuous.comp_continuousOn
          hf).pow 2)
      hrho (fun x hx => hb x (hwφ hx))
    simpa only [E, mul_pow] using hi
  have hHE : (∑ i, ∫ x, (φ x * qH (H (t, x)) i) ^ 2) ≤ E :=
    hcomponent _ hcH (by
      intro x _
      have hA0 := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => sq_nonneg (qA (A (t, x)) i))
      have hS0 := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => sq_nonneg (qS (S (t, x)) i))
      dsimp only [rho]
      linarith)
  have hSE : (∑ i, ∫ x, (φ x * qS (S (t, x)) i) ^ 2) ≤ E :=
    hcomponent _ hcS (by
      intro x _
      exact le_add_of_nonneg_left (add_nonneg
        (Finset.sum_nonneg (fun i _ => sq_nonneg (qH (H (t, x)) i)))
        (Finset.sum_nonneg (fun i _ => sq_nonneg (qA (A (t, x)) i)))))
  have hHrate := hHr.trans (add_le_add hHE (mul_le_mul_of_nonneg_left hSE hCH))
  have hd := canonicalDomain_hasDerivAt_difference_energy U hU qH qA qS
    hφ.continuous hφc hφU F F' R R' hR hR' p t ht
  rw [hd.deriv]
  calc
    _ ≤ (E + CH * E) + (lambda / 8 * D + (CA / (lambda / 8) + CA) * E) +
        (CS * E0 - (5 * lambda / 8) * D) := add_le_add (add_le_add hHrate hAr) hSr
    _ = CS * E0 + L * E - lambda / 2 * D := by dsimp only [L]; ring
    _ ≤ CS * E0 + L * (B * E0) - lambda / 2 * D :=
      sub_le_sub_right (add_le_add le_rfl (mul_le_mul_of_nonneg_left hE hL)) _
    _ = C * E0 - lambda / 2 * D := by dsimp only [C]; ring

end PoincareConjecture.M34
