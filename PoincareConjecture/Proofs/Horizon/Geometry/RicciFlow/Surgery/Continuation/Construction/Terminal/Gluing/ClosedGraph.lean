import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Gluing.Collar

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.MetricSurgeryResult

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] [SecondCountableTopology M]
  {g : RiemannianMetric 3 M} {K : MetricSurgeryConstants}
  {g₀ : StandardInitialMetric} {I : MetricSurgeryInput K g}
  (R : MetricSurgeryResult g₀ I)

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] in
theorem closure_negative_image_subset :
    closure (R.collapse '' (I.negativeHalf : Set M)) ⊆
      R.collapse '' ((I.negativeHalf : Set M) ∪ I.neck.central_sphere) := by
  change closure (R.collapse '' I.neck.region (-I.neck.epsilon⁻¹) 0) ⊆ _
  rw [← R.cap_exterior, closure_eq_self_union_frontier, frontier_compl]
  intro y hy
  rcases hy with hy | hy
  · rw [R.cap_exterior] at hy
    exact image_mono subset_union_left hy
  · have hb := frontier_closure_subset hy
    rw [← R.cap_boundary] at hb
    exact image_mono subset_union_right hb

theorem retained_inverse_continuousAt_closure_negative {y : R.output.carrier}
    (hy : y ∈ closure (R.collapse '' (I.negativeHalf : Set M))) :
    ContinuousAt R.retained_inverse y := by
  obtain ⟨x, hx, rfl⟩ := R.closure_negative_image_subset hy
  have hxc : x ∈ I.retainedCollar := hx.elim
    (fun h => I.negativeHalf_subset_retainedCollar h)
    (fun h => I.centralSphere_subset_retainedCollar h)
  exact ((R.retained_inverse_smooth _ (mem_image_of_mem _ hxc)).contMDiffAt
    ((R.retained_image_isOpen I.retainedCollar subset_rfl).mem_nhds
      (mem_image_of_mem _ hxc))).continuousAt

theorem isClosed_negative_graph (U : Opens M)
    (hU : Disjoint (U : Set M) I.neck.central_sphere) :
    IsClosed {p : U × R.output.carrier |
      p.1.val ∈ I.negativeHalf ∧ R.collapse p.1.val = p.2} := by
  let S : Set (U × R.output.carrier) :=
    {p | p.1.val ∈ I.negativeHalf ∧ R.collapse p.1.val = p.2}
  have hy : ∀ p ∈ closure S,
      p.2 ∈ closure (R.collapse '' (I.negativeHalf : Set M)) := by
    apply closure_minimal
    · intro p hp
      exact subset_closure ⟨p.1.val, hp.1, hp.2⟩
    · exact isClosed_closure.preimage continuous_snd
  have heq : EqOn (fun p : U × R.output.carrier => R.retained_inverse p.2)
      (fun p => p.1.val) S := by
    intro p hp
    change R.retained_inverse p.2 = p.1.val
    rw [← hp.2]
    exact R.retained_left_inverse (I.negativeHalf_subset_retainedCollar hp.1)
  have heqc : EqOn (fun p : U × R.output.carrier => R.retained_inverse p.2)
      (fun p => p.1.val) (closure S) := heq.of_subset_closure
    (fun p hp => ((R.retained_inverse_continuousAt_closure_negative (hy p hp)).comp
      continuous_snd.continuousAt).continuousWithinAt)
    (continuous_subtype_val.comp continuous_fst).continuousOn subset_closure subset_rfl
  apply isClosed_of_closure_subset
  intro p hp
  obtain ⟨x, hx, hxy⟩ := R.closure_negative_image_subset (hy p hp)
  have hxc : x ∈ I.retainedCollar := hx.elim
    (fun h => I.negativeHalf_subset_retainedCollar h)
    (fun h => I.centralSphere_subset_retainedCollar h)
  have hxp : x = p.1.val := by
    rw [← R.retained_left_inverse hxc, hxy]
    exact heqc hp
  have hneg : x ∈ I.negativeHalf := hx.resolve_right (fun hxS =>
    Set.disjoint_left.mp hU (hxp ▸ p.1.property) hxS)
  exact ⟨hxp ▸ hneg, hxp ▸ hxy⟩

end PoincareConjecture.MetricSurgeryResult
