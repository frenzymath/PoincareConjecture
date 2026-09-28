import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderHighMiddleModel
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderUniformScalar
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Regularity
import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.CapTopology.NeckCollar
import Mathlib.Topology.Connected.Clopen










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M28




theorem exists_neck_frontier_exclusion_accuracy :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ (1 / 200 : ℝ) ∧
      ∀ (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [T2Space M]
        (g : RiemannianMetric 3 M) (D : LeviCivitaData g) (W : Set M),
        IsOpen W → IsCompact (frontier W) →
          ∃ B : ℝ, ∀ N : EpsilonNeck g, N.epsilon ≤ epsilon0 →
            N.center ∈ W → B < D.scalarCurvature N.center → N.carrier ⊆ W := by
  obtain ⟨epsilon0, hpos, hsmall, hratio⟩ := tube.exists_cylinder_scalar_ratio_accuracy.{u}
  refine ⟨epsilon0, hpos, hsmall, ?_⟩
  intro M _ _ _ _ g D W hWo hfront
  obtain ⟨B0, hB0⟩ := hfront.bddAbove_image D.continuous_scalarCurvature.continuousOn
  refine ⟨2 * B0, ?_⟩
  intro N heps hcenter hhigh
  have hNc : N.center ∈ N.carrier := N.central_sphere_subset N.center_on_central_sphere
  have hdisj : Disjoint (frontier W) N.carrier := by
    apply disjoint_left.mpr
    intro y hyfront hyN
    have hybound := hB0 (mem_image_of_mem D.scalarCurvature hyfront)
    have hcompare := hratio M g D N heps N.center hNc y hyN
    linarith
  have hregion : N.region (-N.epsilon⁻¹) N.epsilon⁻¹ = N.carrier := by
    ext x
    exact ⟨fun hx => hx.1, fun hx => ⟨hx, (N.coordinate_inverse_mem x hx).2⟩⟩
  have hconnected : IsConnected N.carrier := by
    refine ⟨⟨N.center, hNc⟩, ?_⟩
    rw [← hregion]
    exact N.isPreconnected_region le_rfl le_rfl
  let : ConnectedSpace N.carrier := Subtype.connectedSpace hconnected
  have hclopen : IsClopen ((Subtype.val : N.carrier → M) ⁻¹' W) :=
    isClopen_preimage_val hWo hdisj
  have hfull := hclopen.eq_univ ⟨⟨N.center, hNc⟩, hcenter⟩
  intro y hy
  have hh : (⟨y, hy⟩ : N.carrier) ∈ (univ : Set N.carrier) := mem_univ _
  rw [← hfull] at hh
  exact hh





theorem exists_recut_all_necks_model_accuracy :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ (1 / 200 : ℝ) ∧
      ∀ (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [T2Space M]
        (g : RiemannianMetric 3 M) (D : LeviCivitaData g) (W : Set M),
        IsOpen W → IsCompact (frontier W) → ∀ T : OpenCylinderModel W,
          (∃ B : ℝ, ∀ x ∈ T.tail false (1 / 2), D.scalarCurvature x ≤ B) →
          (∀ B : ℝ, ∃ a ∈ Ioo (0 : ℝ) 1,
            ∀ x ∈ T.tail true a, B < D.scalarCurvature x) →
          ∃ Z : OpenCylinderModel W,
            (∃ B : ℝ, ∀ x ∈ Z.tail false (1 / 2), D.scalarCurvature x ≤ B) ∧
            (∀ B : ℝ, ∃ a ∈ Ioo (0 : ℝ) 1,
              ∀ x ∈ Z.tail true a, B < D.scalarCurvature x) ∧
            ∀ x ∈ Z.tail true (1 / 2), ∀ N : EpsilonNeck g,
              N.epsilon ≤ epsilon0 → N.center = x → N.carrier ⊆ W := by
  obtain ⟨epsilon0, hpos, hsmall, hexclude⟩ := exists_neck_frontier_exclusion_accuracy.{u}
  refine ⟨epsilon0, hpos, hsmall, ?_⟩
  intro M _ _ _ _ g D W hWo hfront T hnegative hdiverge
  obtain ⟨B, hB⟩ := hexclude M g D W hWo hfront
  obtain ⟨Z, hZnegative, hZdiverge, hZhigh⟩ := T.exists_high_midlevel_model
    D.scalarCurvature D.continuous_scalarCurvature.continuousOn hnegative hdiverge B
  refine ⟨Z, hZnegative, hZdiverge, ?_⟩
  intro x hx N heps hcenter
  apply hB N heps
  · rw [hcenter]
    exact Z.tail_subset_m28 true (by norm_num) (by norm_num) hx
  · rw [hcenter]
    exact hZhigh x hx

end PoincareConjecture.M28
