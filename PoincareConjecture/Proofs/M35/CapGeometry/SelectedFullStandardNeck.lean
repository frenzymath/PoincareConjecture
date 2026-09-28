import PoincareConjecture.Proofs.M35.CapGeometry.SelectedFullNeckFamily
import PoincareConjecture.Proofs.M35.Thm12_28.GeneralizedNeck

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.OrdinaryRealization

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem blowupSequence_full_standard_evolving_neck
    (P : M35StandardCapPredecessors) (atlas : StandardCylinderAtlas)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤)) :
    letI : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
    letI : ChartedSpace E3 L.limit.carrier.carrier := L.limit.carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
    ∀ (g : RiemannianMetric 3 L.limit.sliceCarrier.carrier) (N : EpsilonNeck g)
      (_hmetric : g = L.limit.flow.metric 0) (_he : N.epsilon ≤ 1 / 24)
      (_hcenter : N.center = L.limit.base) (_hcompact : IsCompact (closure N.carrier))
      (j : ℕ) (_hstage : closure N.carrier ⊆ L.exhaustion.space j)
      (I J : Set ℝ) (_hJ : IsCompact J) (_hJt : J ⊆ Iic 0) (_hIJ : I ⊆ J)
      (_hclose : RoundCylinderFamilyClose N.epsilon I
        (fun u => roundCylinderPullback (L.limit.flow.metric u) N.coordinate_map)),
      ∀ᶠ k in atTop, Nonempty (StandardEvolvingNeck atlas E.flow (t (L.subsequence k))
        N.epsilon (x (L.subsequence k)) I) := by
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : ChartedSpace E3 L.limit.carrier.carrier := L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  intro g N hmetric he hcenter hcompact j hstage I J hJ hJt hIJ hclose
  subst g
  have hfamily := blowupSequence_full_neck_family_close P E t x ht hR L N he hcompact j
    hstage I J hJ hJt hIJ hclose
  have htime := L.exhaustion.time_cofinal J hJ (by
    intro u hu
    simpa [blowupBackwardInterval] using hJt hu)
  filter_upwards [eventually_ge_atTop j, hfamily, htime] with k hj hk htk
  let Q := (blowupSequence P E t x ht hR).scale (L.subsequence k)
  have hQ : Q = (E.flow.connection (t (L.subsequence k))).scalarCurvature
      (x (L.subsequence k)) := blowupSequence_scale P E t x ht hR (L.subsequence k)
  have hzero : (0 : ℝ) ∈ Icc (-L.exhaustion.time k) 0 :=
    ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩
  have htime₀ : t (L.subsequence k) + 0 / Q ∈ Ico 0 E.flow.base.lifetime :=
    ((L.embedding k).forward 0 hzero L.limit.base).property
  let f := cylinderSpatialCoordinates E.flow.base.flow (L.embedding k)
    (L.exhaustion.space_open k) 0 hzero htime₀
  have hsub : N.carrier ⊆ f.source := fun _ hy =>
    L.exhaustion.space_increasing hj (hstage (subset_closure hy))
  have hbase : f L.limit.base = x (L.subsequence k) := by
    have hb := L.base_preserving k hzero
    exact congrArg (fun p : (generalizedFlow E.flow.base.flow).point => p.2.val) hb
  let patch₀ := N.transportedStandardPatch f hsub
  let patch : StandardCylinderPatch N.epsilon⁻¹ (x (L.subsequence k)) :=
    { patch₀ with
      center_sphere := by
        obtain ⟨q, hq⟩ := patch₀.center_sphere
        exact ⟨q, hq.trans ((congrArg f hcenter).trans hbase)⟩ }
  refine ⟨{
    time_mem := ht (L.subsequence k)
    epsilon_pos := N.epsilon_pos
    epsilon_lt_half := N.epsilon_lt_half
    scalar_pos := E.scalar_pos (ht (L.subsequence k)) (x (L.subsequence k))
    patch := patch
    interval_survival := ?_
    close := ?_
  }⟩
  · intro u hu
    have h := ((L.embedding k).forward u (htk (hIJ hu)) L.limit.base).property
    change t (L.subsequence k) + u / Q ∈ Ico 0 E.flow.base.lifetime at h
    rwa [hQ] at h
  · change RoundCylinderFamilyClose N.epsilon I
      (fun u z v w => Q * roundCylinderPullback
        (E.flow.metric (t (L.subsequence k) + u / Q)) patch.coordinate z v w) at hk
    change RoundCylinderFamilyClose N.epsilon I
      (fun u z v w => (E.flow.connection (t (L.subsequence k))).scalarCurvature
        (x (L.subsequence k)) * roundCylinderPullback
          (E.flow.metric (t (L.subsequence k) + u /
            (E.flow.connection (t (L.subsequence k))).scalarCurvature (x (L.subsequence k))))
          patch.coordinate z v w)
    rwa [hQ] at hk

end PoincareConjecture.M35.OrdinaryRealization
