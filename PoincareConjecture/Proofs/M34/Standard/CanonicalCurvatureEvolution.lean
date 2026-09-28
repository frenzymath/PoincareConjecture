import PoincareConjecture.Proofs.M03.CurvatureRateAbsorption
import PoincareConjecture.Proofs.M34.Standard.CanonicalFlowCurvature
import PoincareConjecture.Proofs.M34.Standard.UniformCanonicalDifferenceFlux
import PoincareConjecture.Proofs.M34.Standard.CurvatureReactionEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set Bundle
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.M34

open DifferenceEnergy

set_option maxHeartbeats 8000000 in

theorem canonicalDomain_curvature_difference_coordinate_pde
    {n dS : ℕ} (U : Set (V n)) (hU : IsOpen U) [Nonempty U]
    (qS : FS n ≃L[ℝ] EuclideanSpace ℝ (Fin dS)) :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ {J J' : Set ℝ} (F : RicciFlow n U J) (F' : RicciFlow n U J')
      (R R' : ℝ → U → FS n),
      (∀ t x u v w, R t x u v w = (F.connection t).curvature x u v w) →
      (∀ t x u v w, R' t x u v w = (F'.connection t).curvature x u v w) →
      ∀ p : U,
        let r := (extChartAt (𝓡 n) p).symm
        let G : ℝ × V n → FH n := fun z => (F.metric z.1).inner (r z.2)
        let G' : ℝ × V n → FH n := fun z => (F'.metric z.1).inner (r z.2)
        let H := fun z => G z - G' z
        let A : ℝ × V n → FA n := fun z => CovariantDerivative.difference
          (F.connection z.1).connection (F'.connection z.1).connection (r z.2)
        let Rbar := fun z : ℝ × V n => R z.1 (r z.2)
        let Rbar' := fun z : ℝ × V n => R' z.1 (r z.2)
        let S := fun z => Rbar z - Rbar' z
        let gamma := fun z : ℝ × V n =>
          (canonicalDomain_differenceEnergyBackground U hU
            (F.metric z.1) (F.connection z.1) p z.2).1.2
        let gamma' := fun z : ℝ × V n =>
          (canonicalDomain_differenceEnergyBackground U hU
            (F'.metric z.1) (F'.connection z.1) p z.2).1.2
        let kp := fun z : ℝ × V n => fun d l j k m =>
          fderiv ℝ (fun y => raw (Rbar' (z.1, y)) l j k m) z.2
            (EuclideanSpace.single d 1) + curvatureAction (gamma' z) d (raw (Rbar' z)) l j k m
        let vp := fun z : ℝ × V n => fun i l j k m => ∑ d : Fin n,
          EuclideanSpace.proj i ((G' z).inverse (EuclideanSpace.proj d)) * kp z d l j k m
        let dS := fun z : ℝ × V n => fun beta : Fin dS × Fin n =>
          fderiv ℝ (fun y => qS (S (z.1, y)) beta.1) z.2 (EuclideanSpace.single beta.2 1)
        let flux := fun z : ℝ × V n => curvatureDifferenceFlux
          (G z).inverse (G' z).inverse (gamma z) (raw (Rbar' z)) (kp z) (H z) (A z) (S z)
        let W := fun z : ℝ × V n => curvatureDifferenceRemainder qS
          (G z).inverse (G' z).inverse (gamma z) (raw (Rbar' z)) (kp z) (vp z)
          (dS z) (H z) (A z) (S z)
        let Q := fun z : ℝ × V n => curvatureContraction qS
          (modelCurvatureReactionDifference (G z) (G' z) (Rbar z) (Rbar' z))
        ∀ t ∈ interior (J ∩ J'),
          (∀ alpha i, ContDiffOn ℝ 1
            (fun y => curvatureContraction qS (flux (t, y) i) alpha) U) ∧
          (∀ alpha, ContinuousOn (fun y => W (t, y) alpha + Q (t, y) alpha) U) ∧
          (∀ alpha, ∀ x ∈ U,
            fderiv ℝ (fun z => qS (S z) alpha) (t, x) (1, 0) =
              (∑ i : Fin n, fderiv ℝ (fun y => ∑ j : Fin n,
                EuclideanSpace.proj i ((G (t, y)).inverse (EuclideanSpace.proj j)) *
                  fderiv ℝ (fun z => qS (S (t, z)) alpha) y (EuclideanSpace.single j 1))
                x (EuclideanSpace.single i 1)) +
              (∑ i : Fin n, fderiv ℝ
                (fun y => curvatureContraction qS (flux (t, y) i) alpha)
                x (EuclideanSpace.single i 1)) + (W (t, x) alpha + Q (t, x) alpha)) := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro J J' F F' R R' hR hR' p r G G' H A Rbar Rbar' S gamma gamma' kp vp dS flux W Q t ht
  have hsymm (x : U) (v : V n) :
      (trivializationAt (V n) (TangentSpace (𝓡 n)) p).symmL ℝ x v = v := by
    rw [constantChart_tangent_symmL (𝓡 n) (canonicalOpen_chart_eq hU)]
    rfl
  have hforward (x : U) (v : TangentSpace (𝓡 n) x) :
      (trivializationAt (V n) (TangentSpace (𝓡 n)) p).continuousLinearMapAt ℝ x v = v := by
    rw [constantChart_tangent_forward (𝓡 n) (canonicalOpen_chart_eq hU)]
    rfl
  have hpde := Proofs.M03.ricciFlow_curvature_bundle_difference_coordinate_pde
    qS J J' F F' R R' hR hR' p t ht
  simp +instances (config := { maxSteps := 2000000 }) only [
    constantChart_bilinear_coordinates (𝓡 n) (canonicalOpen_chart_eq hU),
    constantChart_vectorBilinear_coordinates (𝓡 n) (canonicalOpen_chart_eq hU),
    constantChart_vectorTrilinear_coordinates (𝓡 n) (canonicalOpen_chart_eq hU),
    hsymm, hforward,
    canonicalOpen_chart_target hU] at hpde
  simp +instances (config := { maxSteps := 2000000 }) only
    [r, G, G', H, A, Rbar, Rbar', S, gamma, gamma', kp, vp, dS, flux, W, Q,
    canonicalDomain_differenceEnergyBackground, curvatureDifferenceFlux,
    curvatureDifferenceRemainder, curvatureContraction, divergenceAction, principalFlux,
    connectionRemainder, curvatureAction, modelCurvatureReactionDifference,
    modelCurvatureReaction, modelRicciTrace, raw, ag, EuclideanSpace.coe_proj,
    LinearMap.coe_mk, AddHom.coe_mk,
    extChartAt_coe_symm, modelWithCornersSelf_coe_symm, Function.comp_apply, id_eq,
    map_sub] at hpde ⊢
  constructor
  · exact hpde.1
  constructor
  · exact hpde.2.1
  · exact hpde.2.2

end PoincareConjecture.M34
