import PoincareConjecture.Proofs.M34.Mathlib.UniformCoordinateIntegralEnergy
import PoincareConjecture.Proofs.M34.Standard.CanonicalCurvatureEvolution
import PoincareConjecture.Proofs.M34.Standard.CanonicalPrincipalRegularity
import PoincareConjecture.Proofs.M34.Standard.UniformCanonicalPrincipal
import PoincareConjecture.Proofs.M34.Standard.UniformCanonicalReaction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set MeasureTheory
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.M34

open DifferenceEnergy

set_option maxHeartbeats 2400000 in

theorem exists_uniform_actual_curvature_integral_energy_bound
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
            (∑ alpha : Fin dS, ∫ x, 2 * φ x ^ 2 * qS (S (t, x)) alpha *
              fderiv ℝ (fun z => qS (S z) alpha) (t, x) (1, 0)) ≤
              C * (∫ x in tsupport φ, (∑ i, qH (H (t, x)) i ^ 2) +
                (∑ i, qA (A (t, x)) i ^ 2) + (∑ i, qS (S (t, x)) i ^ 2)) -
                (5 * lambda / 8) * (∑ alpha : Fin dS, ∫ x, φ x ^ 2 *
                  ∑ j : Fin n, (fderiv ℝ (fun y => qS (S (t, y)) alpha) x
                    (EuclideanSpace.single j 1)) ^ 2) := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  let : MeasurableSpace (V n) := borel _
  let : BorelSpace (V n) := ⟨rfl⟩
  classical
  obtain ⟨lambda, CP, hlambda, hCP, hprincipal⟩ :=
    exists_uniform_canonicalDomain_principal_bounds n ha M
  obtain ⟨CF, CW, hCF, hCW, hfluxbound⟩ :=
    exists_uniform_canonicalDomain_differenceFlux_bounds qH qA qS ha M
  obtain ⟨CQ, hCQ, hreaction⟩ := exists_uniform_canonicalDomain_curvatureReaction_bound qH qS ha M
  let CR := CW / (lambda / 8) + CW + CQ
  have hCR : 0 ≤ CR := by dsimp [CR]; positivity
  obtain ⟨C, hC, hlocal⟩ := exists_uniform_coordinate_integral_rate_bound_of_entries
    (I := Fin dS) hU hφ hφc hφU hlambda (zero_le_one.trans hCP) hCF hCR
  refine ⟨lambda, C, hlambda, hC, ?_⟩
  intro J J' F F' R R' hR hR' p r H A S t ht B0 B1 hj0 hj1 he0 he1
  let G : ℝ × V n → FH n := fun z => (F.metric z.1).inner (r z.2)
  let G' : ℝ × V n → FH n := fun z => (F'.metric z.1).inner (r z.2)
  let Rbar := fun z : ℝ × V n => R z.1 (r z.2)
  let Rbar' := fun z : ℝ × V n => R' z.1 (r z.2)
  let gamma := fun z : ℝ × V n =>
    (canonicalDomain_differenceEnergyBackground U hU (F.metric z.1) (F.connection z.1) p z.2).1.2
  let gamma' := fun z : ℝ × V n =>
    (canonicalDomain_differenceEnergyBackground U hU (F'.metric z.1) (F'.connection z.1) p z.2).1.2
  let kp := fun z : ℝ × V n => fun d l j k m =>
    fderiv ℝ (fun y => raw (Rbar' (z.1, y)) l j k m) z.2 (EuclideanSpace.single d 1) +
      curvatureAction (gamma' z) d (raw (Rbar' z)) l j k m
  let vp := fun z : ℝ × V n => fun i l j k m => ∑ d : Fin n,
    EuclideanSpace.proj i ((G' z).inverse (EuclideanSpace.proj d)) * kp z d l j k m
  let gradS := fun z : ℝ × V n => fun beta : Fin dS × Fin n =>
    fderiv ℝ (fun y => qS (S (z.1, y)) beta.1) z.2 (EuclideanSpace.single beta.2 1)
  let flux := fun z : ℝ × V n => curvatureDifferenceFlux
    (G z).inverse (G' z).inverse (gamma z) (raw (Rbar' z)) (kp z) (H z) (A z) (S z)
  let W := fun z : ℝ × V n => curvatureDifferenceRemainder qS
    (G z).inverse (G' z).inverse (gamma z) (raw (Rbar' z)) (kp z) (vp z)
    (gradS z) (H z) (A z) (S z)
  let Q := fun z : ℝ × V n => curvatureContraction qS
    (modelCurvatureReactionDifference (G z) (G' z) (Rbar z) (Rbar' z))
  let f := fun alpha : Fin dS => fun x => qS (S (t, x)) alpha
  let Y := fun alpha : Fin dS => fun x i => curvatureContraction qS (flux (t, x) i) alpha
  let w := fun alpha : Fin dS => fun x => W (t, x) alpha + Q (t, x) alpha
  let rate := fun alpha : Fin dS => fun x => fderiv ℝ (fun z => qS (S z) alpha) (t, x) (1, 0)
  let rho := fun x => (∑ i, qH (H (t, x)) i ^ 2) +
    (∑ i, qA (A (t, x)) i ^ 2) + (∑ i, qS (S (t, x)) i ^ 2)
  let ac := fun x i j => EuclideanSpace.proj i ((G (t, x)).inverse (EuclideanSpace.proj j))
  have hpde := canonicalDomain_curvature_difference_coordinate_pde U hU qS
    F F' R R' hR hR' p t ht
  change (∀ alpha i, ContDiffOn ℝ 1 (fun y => Y alpha y i) U) ∧
    (∀ alpha, ContinuousOn (w alpha) U) ∧
    (∀ alpha, ∀ x ∈ U, rate alpha x =
      (∑ i, fderiv ℝ (fun y => ∑ j, ac y i j *
        fderiv ℝ (f alpha) y (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1)) +
      (∑ i, fderiv ℝ (fun y => Y alpha y i) x (EuclideanSpace.single i 1)) + w alpha x) at hpde
  have hslice : ContDiffOn ℝ ∞ (fun x : V n => (t, x)) U :=
    contDiffOn_const.prodMk contDiffOn_id
  have hH : ContDiffOn (F := FH n) ℝ ∞ H ((J ∩ J') ×ˢ U) :=
    ((canonicalDomain_contDiffOn_flow_metric U hU qH F p).mono
      (Set.prod_mono inter_subset_left subset_rfl)).sub
      ((canonicalDomain_contDiffOn_flow_metric U hU qH F' p).mono
        (Set.prod_mono inter_subset_right subset_rfl))
  have hA := canonicalDomain_contDiffOn_connection_difference U hU qA F F' p
  have hS : ContDiffOn (F := FS n) ℝ ∞ S ((J ∩ J') ×ˢ U) :=
    ((canonicalDomain_contDiffOn_flow_curvature U hU qS F R hR p).mono
      (Set.prod_mono inter_subset_left subset_rfl)).sub
      ((canonicalDomain_contDiffOn_flow_curvature U hU qS F' R' hR' p).mono
        (Set.prod_mono inter_subset_right subset_rfl))
  have hsH := hH.comp hslice (fun _ hx => ⟨interior_subset ht, hx⟩)
  have hsA := hA.comp hslice (fun _ hx => ⟨interior_subset ht, hx⟩)
  have hsS := hS.comp hslice (fun _ hx => ⟨interior_subset ht, hx⟩)
  have hhc (i : Fin dH) : ContDiffOn ℝ ∞ (fun x => qH (H (t, x)) i) U :=
    (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin dH) →L[ℝ] ℝ).contDiff.comp_contDiffOn
      (qH.contDiff.comp_contDiffOn hsH)
  have hac (i : Fin dA) : ContDiffOn ℝ ∞ (fun x => qA (A (t, x)) i) U :=
    (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin dA) →L[ℝ] ℝ).contDiff.comp_contDiffOn
      (qA.contDiff.comp_contDiffOn hsA)
  have hsc (i : Fin dS) : ContDiffOn ℝ ∞ (f i) U :=
    (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin dS) →L[ℝ] ℝ).contDiff.comp_contDiffOn
      (qS.contDiff.comp_contDiffOn hsS)
  have hrho : ContinuousOn rho U :=
    ((continuousOn_finsetSum _ (fun i _ => (hhc i).continuousOn.pow 2)).add
      (continuousOn_finsetSum _ (fun i _ => (hac i).continuousOn.pow 2))).add
      (continuousOn_finsetSum _ (fun i _ => (hsc i).continuousOn.pow 2))
  have hacs (i j : Fin n) : ContDiffOn ℝ 1 (fun x => ac x i j) U :=
    ((canonicalDomain_contDiffOn_principal_entry U hU qH F p i j).comp hslice
      (fun _ hx => ⟨(interior_subset ht).1, hx⟩)).of_le (by simp)
  have hG (x : V n) (hx : x ∈ U) : G (t, x) = B0 x :=
    canonicalDomain_inner_eq_pullbackCoefficients U hU (F.metric t) p x hx
  have hG' (x : V n) (hx : x ∈ U) : G' (t, x) = B1 x :=
    canonicalDomain_inner_eq_pullbackCoefficients U hU (F'.metric t) p x hx
  have hpb (x : V n) (hx : x ∈ tsupport φ) := hprincipal U hU inferInstance
    (F.metric t) (F.connection t) p x (hφU hx) (hj0 x hx) (he0 x hx)
  have hell (x : V n) (hx : x ∈ tsupport φ) (z : Fin n → ℝ) :
      lambda * (∑ i, z i ^ 2) ≤ ∑ i, ∑ j, ac x i j * z i * z j := by
    simpa only [ac, hG x (hφU hx)] using (hpb x hx).2 z
  have hab (x : V n) (hx : x ∈ tsupport φ) (i j : Fin n) : |ac x i j| ≤ CP := by
    simpa only [ac, hG x (hφU hx)] using (hpb x hx).1 i j
  have hraw (x : V n) : raw (Rbar' (t, x)) =
      canonicalDomain_curvatureArray U hU (F'.metric t) (F'.connection t) p x :=
    canonicalDomain_raw_flow_curvature U hU F' R' hR' p t x
  have hkp (x : V n) : kp (t, x) =
      canonicalDomain_covariantCurvatureArray U hU (F'.metric t) (F'.connection t) p x := by
    dsimp only [kp, canonicalDomain_covariantCurvatureArray]
    simp only [hraw, gamma']
  have hvp (x : V n) (hx : x ∈ U) : vp (t, x) =
      canonicalDomain_raisedCurvatureFlux U hU (F'.metric t) (F'.connection t) p x := by
    dsimp only [vp, canonicalDomain_raisedCurvatureFlux]
    rw [hG' x hx, hkp x]
  have hflux (x : V n) (hx : x ∈ U) : flux (t, x) =
      canonicalDomain_curvatureDifferenceFlux U hU (F.metric t) (F.connection t)
        (F'.metric t) (F'.connection t) p x (H (t, x)) (A (t, x)) (S (t, x)) := by
    dsimp only [flux, canonicalDomain_curvatureDifferenceFlux]
    rw [hG x hx, hG' x hx, hraw x, hkp x]
  have hW (x : V n) (hx : x ∈ U) : W (t, x) =
      canonicalDomain_curvatureDifferenceRemainder U hU qS (F.metric t) (F.connection t)
        (F'.metric t) (F'.connection t) p x (gradS (t, x)) (H (t, x)) (A (t, x)) (S (t, x)) := by
    dsimp only [W, canonicalDomain_curvatureDifferenceRemainder]
    rw [hG x hx, hG' x hx, hraw x, hkp x, hvp x hx]
  have hfb (x : V n) (hx : x ∈ tsupport φ) := hfluxbound U hU inferInstance
    (F.metric t) (F.connection t) (F'.metric t) (F'.connection t) p x (hφU hx)
    (hj0 x hx) (hj1 x hx) (he0 x hx) (he1 x hx)
  have hYs (x : V n) (hx : x ∈ tsupport φ) : (∑ alpha, ∑ i, Y alpha x i ^ 2) ≤ CF * rho x := by
    simpa only [Y, hflux x (hφU hx), rho] using
      (hfb x hx).1 (H (t, x)) (A (t, x)) (S (t, x))
  have hWs (x : V n) (hx : x ∈ tsupport φ) : (∑ alpha, 2 * f alpha x * w alpha x) ≤
      lambda / 8 * (∑ alpha, ∑ j, (fderiv ℝ (f alpha) x (EuclideanSpace.single j 1)) ^ 2) +
        CR * rho x := by
    have hw := (hfb x hx).2 (gradS (t, x)) (H (t, x)) (A (t, x)) (S (t, x))
      (lambda / 8) (by positivity)
    rw [← hW x (hφU hx)] at hw
    have hq := hreaction U hU inferInstance (F.metric t) (F.connection t)
      (F'.metric t) (F'.connection t) p x (hφU hx)
      (hj0 x hx) (hj1 x hx) (he0 x hx) (he1 x hx) (Rbar (t, x)) (Rbar' (t, x))
      (canonicalDomain_raw_flow_curvature U hU F R hR p t x) (hraw x)
    have hg0 := hG x (hφU hx)
    have hg1 := hG' x (hφU hx)
    dsimp only [B0, r] at hg0
    dsimp only [B1, r] at hg1
    rw [← hg0, ← hg1] at hq
    have hq' : (∑ alpha, 2 * f alpha x * Q (t, x) alpha) ≤ CQ * rho x := by
      apply hq.trans
      apply mul_le_mul_of_nonneg_left _ hCQ
      have hn := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => sq_nonneg (qA (A (t, x)) i))
      change (∑ i, qH (H (t, x)) i ^ 2) + (∑ i, qS (S (t, x)) i ^ 2) ≤ rho x
      dsimp only [rho]
      linarith
    have hsum := add_le_add hw hq'
    convert hsum using 1
    · rfl
    · simp only [f, w, mul_add, Finset.sum_add_distrib]
    · simp only [rho, f, gradS, CR, Fintype.sum_prod_type]
      ring
  have hfs (x : V n) (_hx : x ∈ tsupport φ) : (∑ i, f i x ^ 2) ≤ rho x := by
    exact le_add_of_nonneg_left (add_nonneg
      (Finset.sum_nonneg (fun i _ => sq_nonneg (qH (H (t, x)) i)))
      (Finset.sum_nonneg (fun i _ => sq_nonneg (qA (A (t, x)) i))))
  have hf2 (i : Fin dS) : ContDiffOn ℝ 2 (f i) U := (hsc i).of_le (by decide)
  have hb := hlocal ac hacs hell hab f hf2 Y hpde.1
    (lambda / 8) w rate hpde.2.1 rho hrho
    (fun x _ => by dsimp [rho]; positivity) hfs hYs hWs hpde.2.2
  have hcoef : 3 * lambda / 4 - lambda / 8 = 5 * lambda / 8 := by ring
  simpa only [f, rate, rho, hcoef] using hb

end PoincareConjecture.M34
