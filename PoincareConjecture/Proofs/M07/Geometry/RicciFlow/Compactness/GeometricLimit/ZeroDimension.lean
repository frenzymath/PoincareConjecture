import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Stages.SpacetimeEmbedding










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture


theorem FlowCarrier.metricComplete_of_dimension_zero (C : FlowCarrier 0) (g : C.metric) :
    C.metricComplete g := by
  let : Subsingleton C.carrier := C.subsingleton_zero
  unfold FlowCarrier.metricComplete
  infer_instance



noncomputable def PointedFlowSequence.geometricConvergence_zero
    {T' T : ℝ} (S : PointedFlowSequence 0 T' T) : PointedGeometricConvergence S := by
  let : ∀ k, TopologicalSpace (S.carrier k).carrier := fun k => (S.carrier k).topologicalSpace
  let : ∀ k, ChartedSpace (EuclideanSpace ℝ (Fin 0)) (S.carrier k).carrier :=
    fun k => (S.carrier k).chartedSpace
  let : ∀ k, IsManifold (𝓡 0) ∞ (S.carrier k).carrier := fun k => (S.carrier k).isManifold
  let : ∀ k, Subsingleton (S.carrier k).carrier := fun k => (S.carrier k).subsingleton_zero
  let e : ∀ k, (S.carrier 0).carrier ≃ₘ⟮𝓡 0, 𝓡 0⟯ (S.carrier k).carrier := fun k =>
    { toEquiv :=
        { toFun := fun _ => (S.flow k).base
          invFun := fun _ => (S.flow 0).base
          left_inv := fun _ => Subsingleton.elim _ _
          right_inv := fun _ => Subsingleton.elim _ _ }
      contMDiff_toFun := contMDiff_const
      contMDiff_invFun := contMDiff_const }
  have hemb (k : ℕ) : Topology.IsOpenEmbedding
      (fun x : (univ : Set (S.carrier 0).carrier) => e k x) :=
    (e k).toHomeomorph.isOpenEmbedding.comp isOpen_univ.isOpenEmbedding_subtypeVal
  have hsmooth (k : ℕ) : IsLocalDiffeomorphOn (𝓡 0) (𝓡 0) ∞ (e k) univ :=
    (e k).isLocalDiffeomorph.isLocalDiffeomorphOn univ
  refine
    { limitCarrier := S.carrier 0
      limitFlow := S.flow 0
      subsequence := id
      subsequence_strictMono := strictMono_id
      exhaustion := fun _ => univ
      exhaustion_open := fun _ => isOpen_univ
      exhaustion_connected := fun _ => (S.carrier 0).connected
      exhaustion_compactClosure := fun _ => by simpa only [closure_univ] using isCompact_univ
      exhaustion_increasing := fun _ => subset_rfl
      exhaustion_covers := iUnion_const univ
      embedding := fun k => SmoothSpacetimeEmbedding.of_spatial (S.flow 0) (S.flow k)
        isOpen_univ (e k) (hemb k) (hsmooth k) (Ioo T' T)
      base_in_exhaustion := fun _ => mem_univ _
      base_preserving := fun _ => rfl
      pullback_metric_converges := ?_
      pullback_metric_CInfinity := ?_ }
  · intro j K I _ _ _ _ ε hε
    refine ⟨j, le_rfl, ?_⟩
    intro k _ t _ x _ v w _ _
    have hv : v = 0 := @Subsingleton.elim (EuclideanSpace ℝ (Fin 0)) _ v 0
    simpa only [pullbackInnerValue, FlowCarrier.metricInner, hv, map_zero, zero_apply,
      sub_self, abs_zero] using hε
  · intro q j r K _ _ ε _
    refine ⟨j, le_rfl, ?_⟩
    intro k _ a
    exact a.elim0



theorem pointedRicciFlowCompactness_zero
    {T' T : ℝ} (H : PointedRicciFlowCompactnessHypotheses 0 T' T) :
    Nonempty (PointedRicciFlowCompactnessConclusion H) := by
  refine ⟨{ geometric_limit := H.sequence.geometricConvergence_zero
            complete_interior := ?_ }⟩
  intro t _
  exact (H.sequence.carrier 0).metricComplete_of_dimension_zero
    ((H.sequence.flow 0).metricAt t)

end PoincareConjecture
