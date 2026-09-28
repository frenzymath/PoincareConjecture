import PoincareConjecture.Proofs.M35.CapGeometry.TransportedCertificate
import PoincareConjecture.Proofs.M35.CapGeometry.FullCoreRadii
import PoincareConjecture.Proofs.M35.CapGeometry.SelectedCoreVolume
import PoincareConjecture.Proofs.M35.Thm12_28.TransportedCapSize
import PoincareConjecture.Proofs.M35.Thm12_28.TransportedCapOperators

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.OrdinaryRealization

theorem blowupSequence_cap_certificate_of_full_neck_comparisons
    (P : M35StandardCapPredecessors) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ {g₀ : StandardInitialMetric}
      (E : RepairedStandardCapExistenceData g₀)
      (NC : StandardFlowNoncollapsingCertificate E.flow)
      (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
      (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
      (_htone : Tendsto t atTop (𝓝 1))
      (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
      (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
        (blowupBackwardInterval ⊤)) (j : ℕ),
    letI : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
    letI : MeasurableSpace L.limit.carrier.carrier := L.limit.carrier.measurableSpace
    letI : BorelSpace L.limit.carrier.carrier := L.limit.carrier.borelSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
      L.limit.carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
    letI : T2Space L.limit.carrier.carrier := L.limit.carrier.t2Space
    letI : T3Space L.limit.carrier.carrier := L.limit.carrier.t3Space
    letI : ConnectedSpace L.limit.carrier.carrier := L.limit.connectedSpace
    ∀ N : CapCertificate (L.limit.flow.metric 0), N.epsilon ≤ delta →
      N.connection = L.limit.flow.connection 0 →
      IsCompact (closure N.carrier) → closure N.carrier ⊆ L.exhaustion.space j →
      (∀ᶠ k in atTop,
        let f : L.limit.carrier.carrier → StandardCapSpace := fun z =>
          ((L.embedding k).forward 0
            ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ z).val
        RoundCylinderClose N.epsilon 0 (fun z v w =>
          (E.flow.connection (t (L.subsequence k))).scalarCurvature (f N.end_neck.center) *
            roundCylinderPullback (E.flow.metric (t (L.subsequence k)))
              (f ∘ N.end_neck.coordinate_map) z v w) ∧
        RoundCylinderClose N.epsilon 0 (fun z v w =>
          (E.flow.connection (t (L.subsequence k))).scalarCurvature (f N.boundary_neck.center) *
            roundCylinderPullback (E.flow.metric (t (L.subsequence k)))
              (f ∘ N.boundary_neck.coordinate_map) z v w)) →
      ∀ᶠ k in atTop,
        let f : L.limit.carrier.carrier → StandardCapSpace := fun z =>
          ((L.embedding k).forward 0
            ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ z).val
        ∃ C : CapCertificate (E.flow.metric (t (L.subsequence k))),
          C.epsilon = N.epsilon ∧
          C.cap_constant = 8 * N.cap_constant + 16 / NC.kappa ∧
          C.connection = E.flow.connection (t (L.subsequence k)) ∧
          C.carrier = f '' N.carrier ∧ C.core = f '' N.core ∧
          C.closed_core = f '' N.closed_core ∧ C.boundary_sphere = f '' N.boundary_sphere ∧
          C.model_kind = N.model_kind := by
  obtain ⟨delta, hdelta, hradii⟩ := blowupSequence_cap_closed_core_curvature_balls P
  refine ⟨delta, hdelta, ?_⟩
  intro g₀ E NC t x ht htone hR L j
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : MeasurableSpace L.limit.carrier.carrier := L.limit.carrier.measurableSpace
  have : BorelSpace L.limit.carrier.carrier := L.limit.carrier.borelSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
    L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  have : T2Space L.limit.carrier.carrier := L.limit.carrier.t2Space
  have : T3Space L.limit.carrier.carrier := L.limit.carrier.t3Space
  have : ConnectedSpace L.limit.carrier.carrier := L.limit.connectedSpace
  intro N hfine hconnection hcompact hU hnecks
  have hballs := hradii E t x ht hR L j N hfine hconnection hcompact hU
  have hballvolume := blowupSequence_cap_curvature_ball_volume_lower
    P E NC t x ht htone hR L j N hconnection hcompact hU
  obtain ⟨ksize, _, hsize⟩ :=
    blowupSequence_cap_size_bounds P E t x ht hR L j N hconnection hcompact hU
  obtain ⟨_, _, B, _, _, _, hB, kratio, _, hratio⟩ :=
    blowupSequence_cap_scalar_control P E t x ht hR L j N hconnection hcompact hU
  obtain ⟨koperators, _, hoperators⟩ :=
    blowupSequence_cap_scalar_operator_bounds P E t x ht hR L j N hconnection hcompact hU
  have hcoreU : N.core ⊆ N.carrier := by
    rw [N.core_eq_interior_closed_core]
    intro y hy
    exact (N.closed_core_eq_complement_end ▸ interior_subset hy).1
  filter_upwards [hnecks, hballs, hballvolume, eventually_ge_atTop j,
    eventually_ge_atTop ksize, eventually_ge_atTop kratio,
    eventually_ge_atTop koperators] with k hnecksK hballsK hballvolumeK hj hks hkr hko
  dsimp only
  have hzero : (0 : ℝ) ∈ Icc (-L.exhaustion.time k) 0 :=
    ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩
  have htime := ((L.embedding k).forward 0 hzero L.limit.base).property
  let phi := cylinderSpatialCoordinates E.flow.base.flow (L.embedding k)
    (L.exhaustion.space_open k) 0 hzero htime
  have hsource : closure N.carrier ⊆ phi.source :=
    hU.trans (L.exhaustion.space_increasing hj)
  apply N.exists_transported_certificate (E.flow.metric (t (L.subsequence k)))
    (E.flow.connection (t (L.subsequence k))) phi hsource NC.kappa NC.kappa_pos
  · intro p _
    exact E.scalar_pos (ht (L.subsequence k)) p
  · exact hnecksK.1
  · exact hnecksK.2
  · exact (hsize k hks).1
  · refine ⟨B, hB, ?_⟩
    rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
    exact (hratio k hkr).2 y (subset_closure hy) z (subset_closure hz)
  · exact (hsize k hks).2
  · rintro _ ⟨y, hy, rfl⟩
    exact hballsK y (N.core_eq_interior_closed_core ▸ hy |> interior_subset)
  · rintro _ ⟨y, hy, rfl⟩ r hr hscale
    exact hballvolumeK y (subset_closure (hcoreU hy)) r hr hscale
  · rintro _ ⟨y, hy, rfl⟩
    exact (hoperators k hko y (subset_closure hy)).1.le
  · rintro _ ⟨y, hy, rfl⟩
    exact (hoperators k hko y (subset_closure hy)).2.le

end PoincareConjecture.M35.OrdinaryRealization
