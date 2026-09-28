import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.Core.Truncation.Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

noncomputable section

namespace PoincareConjecture.CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}

theorem boundary_subset_truncated_end_closure (C : CapCertificate g)
    {d : ℝ} (hd : -C.epsilon⁻¹ < d) :
    C.boundary_sphere ⊆ closure (C.end_neck.region (-C.epsilon⁻¹) d) := by
  intro x hx
  have hquarter : x ∈ closure (C.end_neck.reversed.region
      (C.end_neck.reversed.epsilon⁻¹ / 2) C.end_neck.reversed.epsilon⁻¹) := by
    simpa only [EpsilonNeck.reversed_epsilon, EpsilonNeck.reversed_region,
      C.end_neck_epsilon, neg_div] using C.boundary_subset_negative_end_closure hx
  have hout : x ∉ C.end_neck.reversed.carrier :=
    fun h => disjoint_left.mp C.disjoint_closed_core_end (C.boundary_subset_closed_core hx) h
  have h := C.end_neck.reversed.mem_closure_positive_tail hquarter hout
    (b := -d) (by rw [EpsilonNeck.reversed_epsilon, C.end_neck_epsilon]; linarith)
  simpa only [EpsilonNeck.reversed_epsilon, EpsilonNeck.reversed_region,
    C.end_neck_epsilon, neg_neg] using h

omit [T2Space M] in

theorem same_core_eq_complement_truncated_end (C : CapCertificate g) (b : ℝ) :
    C.closed_core = (C.closed_core ∪ C.end_neck.region (-C.epsilon⁻¹) b) \
      C.end_neck.region (-C.epsilon⁻¹) b := by
  ext x
  constructor
  · intro hx
    exact ⟨Or.inl hx, fun h => disjoint_left.mp C.disjoint_closed_core_end hx h.1⟩
  · rintro ⟨hx | hx, hn⟩
    · exact hx
    · exact (hn hx).elim

theorem exists_same_core_truncated_domain_topology_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
      ∀ C : CapCertificate g, C.epsilon ≤ ε₀ →
      ∀ b d : ℝ, -C.epsilon⁻¹ < b → b < C.epsilon⁻¹ → -C.epsilon⁻¹ < d →
        Nonempty (SingularRegularLimit.CapDomainTopology C.model_kind C.puncture
          (C.closed_core ∪ C.end_neck.region (-C.epsilon⁻¹) b)
          C.closed_core C.core C.boundary_sphere
          (C.end_neck.region (-C.epsilon⁻¹) b)
          (C.end_neck.region (-C.epsilon⁻¹) d)) := by
  obtain ⟨ε₀, hε₀, hsmall, htransport⟩ := exists_smooth_truncation_threshold.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g C hε b d hb hb' hd
  obtain ⟨J, hsource, htarget, hJ, hJi, _⟩ := htransport C hε b ⟨hb, hb'⟩
  let U := C.closed_core ∪ C.end_neck.region (-C.epsilon⁻¹) b
  let E := C.end_neck.region (-C.epsilon⁻¹) b
  have hUopen : IsOpen U := by
    change IsOpen (C.closed_core ∪ C.end_neck.region (-C.epsilon⁻¹) b)
    rw [← htarget]
    exact J.open_target
  have hBU : C.boundary_sphere ⊆ U := fun _ hx => Or.inl (C.boundary_subset_closed_core hx)
  have hKeq : C.closed_core = U \ E := C.same_core_eq_complement_truncated_end b
  have hEeq : E = C.closed_coreᶜ ∩ U := by
    rw [hKeq]
    ext x
    constructor
    · intro hx
      exact ⟨fun h => h.2 hx, Or.inr hx⟩
    · rintro ⟨hn, hU⟩
      by_contra h
      exact hn ⟨hU, h⟩
  have hmodel := C.imageModelEquivalence J (by rw [hsource]) hJ hJi
  have himage : J '' C.carrier = U := by
    rw [← hsource, J.image_source_eq_target, htarget]
  refine ⟨{
    carrier_open := hUopen
    closed_core_compact := C.closed_core_compact
    core_nonempty := C.core_nonempty
    core_eq_interior := C.core_eq_interior_closed_core
    model_equivalence := by
      change CapModelEquivalence C.model_kind C.puncture U
      rw [← himage]
      exact hmodel
    end_subset := subset_union_right
    closed_core_eq_complement_end := hKeq
    boundary_eq_end_frontier := ?_
    boundary_subset_negative_end_closure := C.boundary_subset_truncated_end_closure hd
    boundary_subset := hBU
    core_frontier_eq_boundary := C.core_frontier_eq_boundary
    boundary_local_defining_function := ?_ }⟩
  · change C.boundary_sphere = U ∩ frontier E
    rw [hEeq, inter_comm U, frontier_inter_open_inter hUopen, frontier_compl,
      C.core_frontier_eq_boundary, inter_eq_left.mpr hBU]
  · intro x hx
    obtain ⟨W, f, hW, hxW, _, hlevel, hfzero, hf, hdf⟩ := C.boundary_local_defining_function x hx
    exact ⟨W ∩ U, f, hW.inter hUopen, ⟨hxW, hBU hx⟩, inter_subset_right,
      fun y hy => hlevel y hy.1, hfzero, hf.mono inter_subset_left, hdf⟩

end PoincareConjecture.CapCertificate

namespace PoincareConjecture.SingularRegularLimit

theorem exists_terminal_same_core_truncated_domain_topology_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M]
        {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
        (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
        {t : ℝ} (ht : t ∈ Ico H.reference.tMinus T)
        (C : CapCertificate (F.metric t)), C.epsilon ≤ ε₀ →
        H.reference.inverse t ht '' C.carrier ⊆ H.reference.regularLimitSet →
        ∀ x₀ : H.regularRegion P04, H.reference.forward t ht x₀ ∈ C.core →
        ∀ b d : ℝ, -C.epsilon⁻¹ < b → b < C.epsilon⁻¹ → -C.epsilon⁻¹ < d →
          Nonempty (CapDomainTopology C.model_kind C.puncture
            (H.regularReferencePreimage P04 t ht
              (C.closed_core ∪ C.end_neck.region (-C.epsilon⁻¹) b))
            (H.regularReferencePreimage P04 t ht C.closed_core)
            (H.regularReferencePreimage P04 t ht C.core)
            (H.regularReferencePreimage P04 t ht C.boundary_sphere)
            (H.regularReferencePreimage P04 t ht (C.end_neck.region (-C.epsilon⁻¹) b))
            (H.regularReferencePreimage P04 t ht (C.end_neck.region (-C.epsilon⁻¹) d))) := by
  obtain ⟨ε₀, hε₀, hsmall, htop⟩ :=
    CapCertificate.exists_same_core_truncated_domain_topology_threshold.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ _ F T H P04 t ht C hε hcapture x₀ hx₀ b d hb hb' hd
  obtain ⟨D⟩ := htop C hε b d hb hb' hd
  let U := C.closed_core ∪ C.end_neck.region (-C.epsilon⁻¹) b
  have hUsub : U ⊆ C.carrier := union_subset C.closed_core_subset_carrier
    (fun _ hx => C.end_neck_subset hx.1)
  have hcaptureU : H.reference.inverse t ht '' U ⊆ H.reference.regularLimitSet :=
    (image_mono hUsub).trans hcapture
  refine ⟨{
    carrier_open := H.regularReferencePreimage_open P04 ht D.carrier_open
    closed_core_compact := H.regularReferencePreimage_compact P04 ht x₀ D.closed_core_compact
      ((image_mono C.closed_core_subset_carrier).trans hcapture)
    core_nonempty := ⟨x₀, hx₀⟩
    core_eq_interior := ?_
    model_equivalence := H.regularReferenceModelEquivalence P04 ht x₀ hcaptureU D.model_equivalence
    end_subset := preimage_mono D.end_subset
    closed_core_eq_complement_end := ?_
    boundary_eq_end_frontier := ?_
    boundary_subset_negative_end_closure := ?_
    boundary_subset := preimage_mono D.boundary_subset
    core_frontier_eq_boundary := ?_
    boundary_local_defining_function := H.regularReferencePreimage_local_defining_function
      P04 ht x₀ subset_union_left hcaptureU D.boundary_local_defining_function }⟩
  · rw [← H.regularReferencePreimage_interior P04 ht, ← D.core_eq_interior]
  · exact congrArg (H.regularReferencePreimage P04 t ht) D.closed_core_eq_complement_end
  · rw [D.boundary_eq_end_frontier, ← H.regularReferencePreimage_frontier P04 ht]
    rfl
  · rw [← H.regularReferencePreimage_closure P04 ht]
    exact preimage_mono D.boundary_subset_negative_end_closure
  · rw [← H.regularReferencePreimage_frontier P04 ht, D.core_frontier_eq_boundary]

end PoincareConjecture.SingularRegularLimit
