import PoincareConjecture.Proofs.M34.Mathlib.CutoffIntegralComparison
import PoincareConjecture.Proofs.M34.Standard.ActualConnectionSpacetimeEnergy
import PoincareConjecture.Proofs.M34.Standard.CanonicalDifferenceRegularity











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set MeasureTheory
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.M34

open DifferenceEnergy

set_option maxHeartbeats 1600000 in



theorem exists_uniform_actual_connection_integral_energy_bound
    {n dH dA dS : ℕ} (U : Set (V n)) (hU : IsOpen U) [Nonempty U]
    (qH : FH n ≃L[ℝ] EuclideanSpace ℝ (Fin dH))
    (qA : FA n ≃L[ℝ] EuclideanSpace ℝ (Fin dA))
    (qS : FS n ≃L[ℝ] EuclideanSpace ℝ (Fin dS))
    {φ : V n → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) {a : ℝ} (ha : 0 < a) (M : ℝ) :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    letI : MeasurableSpace (V n) := borel _
    letI : BorelSpace (V n) := ⟨rfl⟩
    ∃ C : ℝ, 0 ≤ C ∧
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
            ∀ ε : ℝ, 0 < ε →
              (∑ alpha : Fin dA, ∫ x, 2 * φ x ^ 2 * qA (A (t, x)) alpha *
                fderiv ℝ (fun z => qA (A z) alpha) (t, x) (1, 0)) ≤
                ε * (∑ alpha : Fin dS, ∫ x, φ x ^ 2 *
                  ∑ j : Fin n, (fderiv ℝ (fun y => qS (S (t, y)) alpha) x
                    (EuclideanSpace.single j 1)) ^ 2) +
                  (C / ε + C) * (∫ x, φ x ^ 2 *
                    ((∑ i, qH (H (t, x)) i ^ 2) + (∑ i, qA (A (t, x)) i ^ 2) +
                      (∑ i, qS (S (t, x)) i ^ 2))) := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  let : MeasurableSpace (V n) := borel _
  let : BorelSpace (V n) := ⟨rfl⟩
  classical
  obtain ⟨C, hC, hbound⟩ := exists_uniform_actual_connection_spacetime_energy_bound qH qA qS ha M
  refine ⟨C, hC, ?_⟩
  intro J J' F F' R R' hR hR' p r H A S t ht B0 B1 hj0 hj1 he0 he1 ε hε
  obtain ⟨hsH, hsA, hsS⟩ := canonicalDomain_contDiffOn_difference_coordinates U hU
    qH qA qS F F' R R' hR hR' p
  have hcoord {d : ℕ} (f : ℝ × V n → EuclideanSpace ℝ (Fin d))
      (hf : ContDiffOn ℝ ∞ f ((J ∩ J') ×ˢ U)) (i : Fin d) :
      ContDiffOn ℝ ∞ (fun z => f z i) ((J ∩ J') ×ˢ U) :=
    (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).contDiff.comp_contDiffOn hf
  have hslice : ContDiffOn ℝ ∞ (fun x : V n => (t, x)) U :=
    contDiffOn_const.prodMk contDiffOn_id
  have hmap : MapsTo (fun x : V n => (t, x)) U ((J ∩ J') ×ˢ U) :=
    fun _ hx => ⟨interior_subset ht, hx⟩
  have hhc (i : Fin dH) : ContDiffOn ℝ ∞ (fun x => qH (H (t, x)) i) U :=
    (hcoord _ hsH i).comp hslice hmap
  have hac (i : Fin dA) : ContDiffOn ℝ ∞ (fun x => qA (A (t, x)) i) U :=
    (hcoord _ hsA i).comp hslice hmap
  have hsc (i : Fin dS) : ContDiffOn ℝ ∞ (fun x => qS (S (t, x)) i) U :=
    (hcoord _ hsS i).comp hslice hmap
  let rate := fun i : Fin dA => fun x => fderiv ℝ (fun z => qA (A z) i) (t, x) (1, 0)
  let grad := fun i : Fin dS => fun x =>
    ∑ j : Fin n, (fderiv ℝ (fun y => qS (S (t, y)) i) x (EuclideanSpace.single j 1)) ^ 2
  let rho := fun x => (∑ i, qH (H (t, x)) i ^ 2) +
    (∑ i, qA (A (t, x)) i ^ 2) + (∑ i, qS (S (t, x)) i ^ 2)
  have hrate (i : Fin dA) : ContinuousOn (rate i) U := by
    have hi := (hcoord _ hsA i).mono (Set.prod_mono interior_subset (Subset.refl U))
    exact ((hi.continuousOn_fderiv_of_isOpen (isOpen_interior.prod hU) (by decide)).clm_apply
      continuousOn_const).comp (continuous_const.prodMk continuous_id).continuousOn
        (fun _ hx => ⟨ht, hx⟩)
  have hgrad (i : Fin dS) : ContinuousOn (grad i) U :=
    continuousOn_finsetSum _ (fun j _ =>
      (((hsc i).continuousOn_fderiv_of_isOpen hU (by decide)).clm_apply continuousOn_const).pow 2)
  have hrho : ContinuousOn rho U :=
    ((continuousOn_finsetSum _ (fun i _ => (hhc i).continuousOn.pow 2)).add
      (continuousOn_finsetSum _ (fun i _ => (hac i).continuousOn.pow 2))).add
      (continuousOn_finsetSum _ (fun i _ => (hsc i).continuousOn.pow 2))
  have hwc : HasCompactSupport (fun x => φ x ^ 2) :=
    hφc.comp_left (g := fun r : ℝ => r ^ 2) (by simp)
  have hwφ : tsupport (fun x => φ x ^ 2) ⊆ tsupport φ := by
    simpa only [pow_two] using tsupport_mul_subset_left (f := φ) (g := φ)
  have hgi (i : Fin dS) : Integrable (fun x => φ x ^ 2 * grad i x) :=
    integrable_cutoff_mul hU (hφ.pow 2).continuousOn hwc (hwφ.trans hφU) (hgrad i)
  have hri : Integrable (fun x => φ x ^ 2 * rho x) :=
    integrable_cutoff_mul hU (hφ.pow 2).continuousOn hwc (hwφ.trans hφU) hrho
  have hint := integral_cutoff_mul_finsetSum_le (μ := volume) (w := fun x => φ x ^ 2)
    (Finset.univ : Finset (Fin dA))
    hU (hφ.pow 2).continuousOn hwc (hwφ.trans hφU) (fun x _ => sq_nonneg (φ x))
    (q := fun i x => 2 * qA (A (t, x)) i * rate i x)
    (g := fun x => ε * (∑ i, grad i x) + (C / ε + C) * rho x)
    (fun i _ => (continuousOn_const.mul (hac i).continuousOn).mul (hrate i))
    ((continuousOn_const.mul (continuousOn_finsetSum _ (fun i _ => hgrad i))).add
      (continuousOn_const.mul hrho)) (by
        intro x hx
        have hxφ := hwφ hx
        simpa only [rate, grad, rho, Fintype.sum_prod_type] using
          hbound U hU inferInstance F F' R R' hR hR' p t ht x (hφU hxφ)
            (hj0 x hxφ) (hj1 x hxφ) (he0 x hxφ) (he1 x hxφ) ε hε)
  have heq : (fun x => φ x ^ 2 * (ε * (∑ i, grad i x) + (C / ε + C) * rho x)) =
      fun x => ε * (∑ i, φ x ^ 2 * grad i x) + (C / ε + C) * (φ x ^ 2 * rho x) := by
    funext x
    rw [← Finset.mul_sum]
    ring
  rw [heq, integral_add ((integrable_finsetSum _ (fun i _ => hgi i)).const_mul ε)
    (hri.const_mul (C / ε + C)), integral_const_mul, integral_const_mul,
    integral_finsetSum _ (fun i _ => hgi i)] at hint
  simpa only [rate, grad, rho, mul_assoc, mul_left_comm, mul_comm] using hint

end PoincareConjecture.M34
