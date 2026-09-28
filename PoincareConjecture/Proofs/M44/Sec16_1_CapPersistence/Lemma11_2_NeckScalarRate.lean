import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_NeckFourJets
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_ScalarPullback
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_ScalarScaling

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M44

open PoincareConjecture.M36

local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem exists_neck_scalar_evolution_bound (P : M44CapPersistencePredecessors.{u}) :
    ∃ C : ℝ, 0 < C ∧ ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [T2Space M]
      {g : RiemannianMetric 3 M} (N : EpsilonNeck g),
      N.epsilon ≤ 1 / 36 → 4 ≤ ⌊N.epsilon⁻¹⌋₊ → ∀ x ∈ N.carrier,
        |N.connection.laplacian N.connection.scalarCurvature x +
          2 * N.connection.ricciNormSq x| ≤
            C * N.connection.scalarCurvature N.center ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := exists_centeredNeck_scalar_evolution_bound
  refine ⟨C, hC, ?_⟩
  intro M _ _ _ _ g N hsmall horder x hx
  let z := N.coordinate_inverse x
  have hz : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    (N.coordinate_inverse_mem x hx).2
  have hzero := zero_mem_centeredNeckDomain N hz
  obtain ⟨gE, DE, V, hV, hV0, hVD, hmetric⟩ :=
    exists_centeredNeckMetric_realization N z.1 z.2 hzero
  have hcoeff : gE.euclideanCoefficients =ᶠ[𝓝 0]
      centeredCylinderMetric (fun q v w => normalizedNeckForm N q v w) z.1 z.2 := by
    filter_upwards [hV.mem_nhds hV0] with q hq
    exact (hmetric q hq).trans (normalizedNeckMetric_pullbackCoefficients N z.1 z.2
      (hVD hq))
  have hlocal := hbound N hsmall horder z hz gE DE hcoeff
  have hevolution := scalar_evolution_eq_of_metric_pullback DE (normalizedNeckConnection N)
    hV (fun q hq => (centeredNeckLift_contMDiffAt N z.1 z.2 (hVD hq)).contMDiffWithinAt)
    (fun q hq => centeredNeckLift_mfderiv_isInvertible N z.1 z.2 (hVD hq))
    (fun q hq v w => congrArg (fun B : E →L[ℝ] E →L[ℝ] ℝ => B v w) (hmetric q hq))
    hV0 (scalar_smooth_of_predecessors P (normalizedNeckConnection N) _)
  have hpoint : centeredNeckLift N z.1 z.2 0 = x := by
    rw [centeredNeckLift_zero]
    exact neck_coordinate_inverse N hx
  rw [hevolution, hpoint] at hlocal
  have hscale := rescaled_scalar_evolution N.connection N.scalar_center_pos x
    (scalar_smooth_of_predecessors P N.connection)
  change (normalizedNeckConnection N).laplacian
      (normalizedNeckConnection N).scalarCurvature x +
      2 * (normalizedNeckConnection N).ricciNormSq x = _ at hscale
  rw [hscale, abs_div, abs_of_pos (sq_pos_of_pos N.scalar_center_pos)] at hlocal
  exact (div_le_iff₀ (sq_pos_of_pos N.scalar_center_pos)).mp hlocal

theorem canonical_epsilon_fourJet_order {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hsmall : epsilon ≤ 1 / 200) :
    epsilon ≤ 1 / 36 ∧ 4 ≤ ⌊epsilon⁻¹⌋₊ := by
  refine ⟨by linarith, Nat.le_floor ?_⟩
  have hinv : (4 : ℝ) ≤ epsilon⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ hepsilon]
    linarith
  exact hinv

theorem exists_neck_scalar_rate_within (P : M44CapPersistencePredecessors.{u}) :
    ∃ C : ℝ, 0 < C ∧ ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M] [T2Space M]
      {J : Set ℝ} (F : RicciFlow 3 M J) {t : ℝ}, t ∈ J →
      ∀ (N : EpsilonNeck (F.metric t)), N.epsilon ≤ 1 / 200 →
        N.connection = F.connection t → ∃ d : ℝ,
          HasDerivWithinAt (fun s => (F.connection s).scalarCurvature N.center) d J t ∧
            |d| ≤ C * (F.connection t).scalarCurvature N.center ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := exists_neck_scalar_evolution_bound P
  refine ⟨C, hC, ?_⟩
  intro M _ _ _ _ J F t ht N hsmall hconnection
  obtain ⟨hepsilon, horder⟩ := canonical_epsilon_fourJet_order N.epsilon_pos hsmall
  have h := hbound N hepsilon horder N.center
    (N.central_sphere_subset N.center_on_central_sphere)
  rw [hconnection] at h
  exact ⟨_, P.curvature.scalar_evolution 3 M J F t ht N.center, h⟩

end PoincareConjecture.M44
