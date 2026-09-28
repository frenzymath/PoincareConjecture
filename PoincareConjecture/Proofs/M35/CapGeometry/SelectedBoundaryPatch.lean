import PoincareConjecture.Proofs.M35.CapGeometry.ScaledNeckComparison
import PoincareConjecture.Proofs.M35.Thm12_28.TransportedNeckPatch










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.OrdinaryRealization




theorem blowupSequence_boundary_neck_patch (P : M35StandardCapPredecessors)
    (atlas : StandardCylinderAtlas) {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤)) :
    letI : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
      L.limit.carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
    ∀ (N : EpsilonNeck (L.limit.flow.metric 0)) (j : ℕ)
      (_hstage : closure N.carrier ⊆ L.exhaustion.space j)
      (epsilon : ℝ) (_he : 0 < epsilon) (_hde : N.epsilon ≤ epsilon / 4),
      ∀ᶠ k in atTop,
        let f : L.limit.sliceCarrier.carrier → StandardCapSpace := fun z =>
          ((L.embedding k).forward 0
            ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ z).val
        let Q := (blowupSequence P E t x ht hR).scale (L.subsequence k)
        ∃ patch : StandardCylinderPatch epsilon⁻¹ (f N.center),
          patch.coordinate = f ∘ N.coordinate_map ∧
          patch.carrier ⊆ f '' N.carrier ∧
          StandardSpatialCylinderClose atlas (E.flow.metric (t (L.subsequence k)))
            epsilon (N.scale⁻¹ ^ 2 * Q) patch := by
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
    L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  intro N j hstage epsilon he hde
  have hS : 0 < N.scale⁻¹ ^ 2 := sq_pos_of_pos (inv_pos.mpr N.scale_pos)
  have hspace : MapsTo N.coordinate_map (univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
      (L.exhaustion.space j) := fun _ hz =>
    hstage (subset_closure (N.coordinatePartialDiffeomorph.map_source hz))
  have hC : RoundCylinderFamilyClose N.epsilon ({0} : Set ℝ)
      (fun u z v w => N.scale⁻¹ ^ 2 *
        roundCylinderPullback (L.limit.flow.metric u) N.coordinate_map z v w) := by
    obtain ⟨hsmooth, b, hb, hbound⟩ := N.metric_comparison.close
    refine ⟨?_, b, hb, ?_⟩
    · intro u hu
      rcases mem_singleton_iff.mp hu with rfl
      exact hsmooth
    · intro u hu z hz
      rcases mem_singleton_iff.mp hu with rfl
      exact hbound z hz
  obtain ⟨K, hK⟩ := blowupSequence_scaled_neck_family_close P E t x ht hR L
    N.coordinate_map N.epsilon epsilon (N.scale⁻¹ ^ 2) N.epsilon_pos he hS hde
    N.coordinate_map_smooth j hspace ({0} : Set ℝ) ({0} : Set ℝ)
    isCompact_singleton (by simp) subset_rfl hC
  filter_upwards [eventually_ge_atTop j, eventually_ge_atTop K] with k hj hk
  have hzero : (0 : ℝ) ∈ Icc (-L.exhaustion.time k) 0 :=
    ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩
  have htime := ((L.embedding k).forward 0 hzero L.limit.base).property
  let phi := cylinderSpatialCoordinates E.flow.base.flow (L.embedding k)
    (L.exhaustion.space_open k) 0 hzero htime
  let f : L.limit.carrier.carrier → StandardCapSpace := fun z =>
    ((L.embedding k).forward 0 hzero z).val
  have hsub : N.carrier ⊆ phi.source := fun _ hy =>
    L.exhaustion.space_increasing hj (hstage (subset_closure hy))
  have hlength : epsilon⁻¹ ≤ N.epsilon⁻¹ := inv_anti₀ N.epsilon_pos (by linarith)
  let patch := (N.transportedStandardPatch phi hsub).restrict (inv_pos.mpr he) hlength
  refine ⟨patch, rfl, ?_, ?_⟩
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := patch.coordinate_image.symm ▸ hy
    have hzold : z ∈ univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
      ⟨mem_univ _, (neg_le_neg hlength).trans_lt hz.2.1, hz.2.2.trans_le hlength⟩
    exact ⟨N.coordinate_map z, N.coordinatePartialDiffeomorph.map_source hzold, rfl⟩
  · obtain ⟨hsmooth, b, hb, hbound⟩ := hK k hk
    have hclose₀ : RoundCylinderClose epsilon 0
        (fun z v w => (N.scale⁻¹ ^ 2 * (blowupSequence P E t x ht hR).scale (L.subsequence k)) *
          roundCylinderPullback (E.flow.metric (t (L.subsequence k) +
            0 / (blowupSequence P E t x ht hR).scale (L.subsequence k)))
            (f ∘ N.coordinate_map) z v w) :=
      ⟨hsmooth 0 (mem_singleton 0), b, hb, hbound 0 (mem_singleton 0)⟩
    have hclose : RoundCylinderClose epsilon 0
        (fun z v w => (N.scale⁻¹ ^ 2 * (blowupSequence P E t x ht hR).scale (L.subsequence k)) *
          roundCylinderPullback (E.flow.metric (t (L.subsequence k)))
            (f ∘ N.coordinate_map) z v w) := by
      simpa only [zero_div, add_zero] using hclose₀
    exact hclose

end PoincareConjecture.M35.OrdinaryRealization
