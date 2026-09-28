import PoincareConjecture.Proofs.M33.TerminalPolicy

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable {g₀ : StandardInitialMetric} {K : MetricSurgeryConstants}
  {P : SurgeryParameters} {slice : ℝ → GeneralizedSliceCarrier.{u}}
  {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {T : ℝ}
  {E : SurgeryEventData g₀ K P slice metric T}

theorem SurgeryEventData.limit_inverse_image_component
    (E : SurgeryEventData g₀ K P slice metric T)
    {x : E.terminal.carrier} (hC : IsCompact (connectedComponent x)) :
    E.limit_identify.inverse '' connectedComponent x =
      connectedComponent (E.limit_identify.inverse x) := by
  let : LocallyConnectedSpace E.terminal.carrier :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) E.terminal.carrier
  have hg : Continuous E.limit_identify.inverse :=
    continuousOn_univ.1 E.limit_identify.inverse_smooth.continuousOn
  have hgU (z : E.terminal.carrier) : E.limit_identify.inverse z ∈ E.regular_limit := by
    exact E.limit_identify.inverse_image.subset ⟨z, Set.mem_univ z, rfl⟩
  have hset : E.limit_identify.inverse '' connectedComponent x =
      E.regular_limit ∩ E.limit_identify.map ⁻¹' connectedComponent x := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hgU y, by
        simpa only [Set.mem_preimage, E.limit_identify.right_inverse (Set.mem_univ y)] using hy⟩
    · rintro ⟨hz, hfz⟩
      exact ⟨E.limit_identify.map z, hfz, E.limit_identify.left_inverse hz⟩
  have hopen : IsOpen (E.limit_identify.inverse '' connectedComponent x) := by
    rw [hset]
    exact E.limit_identify.map_smooth.continuousOn.isOpen_inter_preimage
      E.regular_limit_open isOpen_connectedComponent
  have hcompact := hC.image hg
  have hconnected := (isConnected_connectedComponent (x := x)).image E.limit_identify.inverse
    hg.continuousOn
  have hx : E.limit_identify.inverse x ∈ E.limit_identify.inverse '' connectedComponent x :=
    ⟨x, mem_connectedComponent, rfl⟩
  exact Set.Subset.antisymm (hconnected.subset_connectedComponent hx)
    ((show IsClopen _ from ⟨hcompact.isClosed, hopen⟩).connectedComponent_subset hx)

theorem SurgeryEventTerminalPolicy.compact_pre_component_subset_interior
    (policy : SurgeryEventTerminalPolicy E)
    {x : E.terminal.carrier} (hC : IsCompact (connectedComponent x))
    (hlow : ∃ y ∈ connectedComponent x,
      E.limit_connection.scalarCurvature y ≤ (P.delta T * P.r T)⁻¹ ^ 2) :
    connectedComponent (E.limit_identify.inverse x) ⊆ interior E.retained_pre := by
  let : LocallyConnectedSpace (slice E.tMinus).carrier :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) (slice E.tMinus).carrier
  apply isOpen_connectedComponent.subset_interior_iff.2
  rw [← E.limit_inverse_image_component hC]
  rintro z ⟨y, hy, rfl⟩
  obtain ⟨w, hw, hwy⟩ := policy.compact_component_retained hC hlow hy
  rw [← hwy, E.limit_identify.left_inverse (E.retained_pre_subset hw)]
  exact hw

theorem SurgeryEventTerminalPolicy.compact_retention_image_disjoint_cap
    (policy : SurgeryEventTerminalPolicy E)
    {x : E.terminal.carrier} (hC : IsCompact (connectedComponent x))
    (hlow : ∃ y ∈ connectedComponent x,
      E.limit_connection.scalarCurvature y ≤ (P.delta T * P.r T)⁻¹ ^ 2)
    (i : Fin E.cap_count) :
    Disjoint (E.retention.map '' connectedComponent (E.limit_identify.inverse x))
      (E.caps i).carrier := by
  have hD := policy.compact_pre_component_subset_interior hC hlow
  refine Set.disjoint_left.2 ?_
  rintro z ⟨y, hy, rfl⟩ hcap
  have hyret := interior_subset (hD hy)
  have hpost : E.retention.map y ∈ E.retained_post := by
    exact E.retention.map_image.subset ⟨y, hyret, rfl⟩
  have hboundary : E.retention.map y ∈ frontier (E.caps i).carrier := by
    rw [← E.cap_boundary i]
    exact ⟨hpost, hcap⟩
  rw [← E.boundary_correspondence i] at hboundary
  obtain ⟨w, hw, heq⟩ := hboundary
  have hwfront : w ∈ frontier E.retained_pre := by
    rw [E.pre_boundary]
    exact Set.mem_iUnion.2 ⟨i, hw⟩
  have hwret : w ∈ E.retained_pre :=
    E.retained_pre_compact.isClosed.closure_eq ▸ frontier_subset_closure hwfront
  have hwy : w = y := by
    have := congrArg E.retention.inverse heq
    simpa only [E.retention.left_inverse hwret, E.retention.left_inverse hyret] using this
  subst w
  exact (mem_frontier_iff_notMem_interior hyret).1 hwfront (hD hy)

theorem SurgeryEventTerminalPolicy.compact_retention_image_component
    (policy : SurgeryEventTerminalPolicy E)
    {x : E.terminal.carrier} (hC : IsCompact (connectedComponent x))
    (hlow : ∃ y ∈ connectedComponent x,
      E.limit_connection.scalarCurvature y ≤ (P.delta T * P.r T)⁻¹ ^ 2) :
    E.retention.map '' connectedComponent (E.limit_identify.inverse x) =
      connectedComponent (E.retention.map (E.limit_identify.inverse x)) := by
  let : LocallyConnectedSpace (slice E.tMinus).carrier :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) (slice E.tMinus).carrier
  let O : Set (slice T).carrier := (⋃ i, (E.caps i).carrier)ᶜ
  have hO : IsOpen O :=
    (isClosed_iUnion_of_finite fun i => (E.caps i).carrier_compact.isClosed).isOpen_compl
  have hOret : O ⊆ E.retained_post := by
    intro z hz
    have hcover : z ∈ E.retained_post ∪ (⋃ i, (E.caps i).carrier) := by
      rw [E.post_cover]
      exact Set.mem_univ z
    exact hcover.resolve_right hz
  have hD : connectedComponent (E.limit_identify.inverse x) ⊆ E.retained_pre :=
    (policy.compact_pre_component_subset_interior hC hlow).trans interior_subset
  have ha := E.retention.map_smooth.continuousOn.mono hD
  have hset : E.retention.map '' connectedComponent (E.limit_identify.inverse x) =
      O ∩ E.retention.inverse ⁻¹' connectedComponent (E.limit_identify.inverse x) := by
    ext z
    constructor
    · intro hz
      obtain ⟨y, hy, rfl⟩ := hz
      constructor
      · intro hcap
        obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hcap
        exact Set.disjoint_left.1
          (policy.compact_retention_image_disjoint_cap hC hlow i) ⟨y, hy, rfl⟩ hi
      · simpa only [Set.mem_preimage, E.retention.left_inverse (hD hy)] using hy
    · rintro ⟨hzO, hzD⟩
      exact ⟨E.retention.inverse z, hzD, E.retention.right_inverse (hOret hzO)⟩
  have hopen : IsOpen (E.retention.map '' connectedComponent (E.limit_identify.inverse x)) := by
    rw [hset]
    exact (E.retention.inverse_smooth.continuousOn.mono hOret).isOpen_inter_preimage
      hO isOpen_connectedComponent
  have hcompactD : IsCompact (connectedComponent (E.limit_identify.inverse x)) := by
    rw [← E.limit_inverse_image_component hC]
    exact hC.image (continuousOn_univ.1 E.limit_identify.inverse_smooth.continuousOn)
  have hcompact := hcompactD.image_of_continuousOn ha
  have hconnected := (isConnected_connectedComponent
    (x := E.limit_identify.inverse x)).image E.retention.map ha
  have hx : E.retention.map (E.limit_identify.inverse x) ∈
      E.retention.map '' connectedComponent (E.limit_identify.inverse x) :=
    ⟨E.limit_identify.inverse x, mem_connectedComponent, rfl⟩
  exact Set.Subset.antisymm (hconnected.subset_connectedComponent hx)
    ((show IsClopen _ from ⟨hcompact.isClosed, hopen⟩).connectedComponent_subset hx)

theorem SurgeryEventTerminalPolicy.compact_post_component_subset_interior
    (policy : SurgeryEventTerminalPolicy E)
    {x : E.terminal.carrier} (hC : IsCompact (connectedComponent x))
    (hlow : ∃ y ∈ connectedComponent x,
      E.limit_connection.scalarCurvature y ≤ (P.delta T * P.r T)⁻¹ ^ 2) :
    connectedComponent (E.retention.map (E.limit_identify.inverse x)) ⊆
      interior E.retained_post := by
  let : LocallyConnectedSpace (slice T).carrier :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) (slice T).carrier
  apply isOpen_connectedComponent.subset_interior_iff.2
  rw [← policy.compact_retention_image_component hC hlow]
  rintro z ⟨y, hy, rfl⟩
  exact E.retention.map_image.subset ⟨y,
    interior_subset (policy.compact_pre_component_subset_interior hC hlow hy), rfl⟩

def SurgeryEventTerminalPolicy.compactComponentEquivalence
    (policy : SurgeryEventTerminalPolicy E)
    {x : E.terminal.carrier} (hC : IsCompact (connectedComponent x))
    (hlow : ∃ y ∈ connectedComponent x,
      E.limit_connection.scalarCurvature y ≤ (P.delta T * P.r T)⁻¹ ^ 2) :
    SurgeryRegionEquivalence E.terminal (slice T) (connectedComponent x)
      (connectedComponent (E.retention.map (E.limit_identify.inverse x))) := by
  have hD : connectedComponent (E.limit_identify.inverse x) ⊆ E.retained_pre :=
    (policy.compact_pre_component_subset_interior hC hlow).trans interior_subset
  have hG : Set.MapsTo E.limit_identify.inverse (connectedComponent x)
      (connectedComponent (E.limit_identify.inverse x)) := by
    intro z hz
    exact (E.limit_inverse_image_component hC).subset ⟨z, hz, rfl⟩
  have hB : Set.MapsTo E.retention.inverse
      (connectedComponent (E.retention.map (E.limit_identify.inverse x)))
      (connectedComponent (E.limit_identify.inverse x)) := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := (policy.compact_retention_image_component hC hlow).symm.subset hz
    simpa only [E.retention.left_inverse (hD hy)] using hy
  refine
    { map := E.retention.map ∘ E.limit_identify.inverse
      inverse := E.limit_identify.map ∘ E.retention.inverse
      map_image := ?_
      inverse_image := ?_
      left_inverse := ?_
      right_inverse := ?_
      map_smooth := ?_
      inverse_smooth := ?_ }
  · change (fun z => E.retention.map (E.limit_identify.inverse z)) '' connectedComponent x = _
    rw [← Set.image_image E.retention.map E.limit_identify.inverse (connectedComponent x),
      E.limit_inverse_image_component hC,
      policy.compact_retention_image_component hC hlow]
  · ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨w, hw, heq⟩ := (E.limit_inverse_image_component hC).symm.subset (hB hy)
      change E.limit_identify.map (E.retention.inverse y) ∈ connectedComponent x
      rw [← heq, E.limit_identify.right_inverse (Set.mem_univ w)]
      exact hw
    · intro hz
      refine ⟨E.retention.map (E.limit_identify.inverse z), ?_, ?_⟩
      · exact (policy.compact_retention_image_component hC hlow).subset
          ⟨E.limit_identify.inverse z, hG hz, rfl⟩
      · simp only [Function.comp_apply, E.retention.left_inverse (hD (hG hz)),
          E.limit_identify.right_inverse (Set.mem_univ z)]
  · intro z hz
    simp only [Function.comp_apply, E.retention.left_inverse (hD (hG hz)),
      E.limit_identify.right_inverse (Set.mem_univ z)]
  · intro z hz
    simp only [Function.comp_apply,
      E.limit_identify.left_inverse (E.retained_pre_subset (hD (hB hz)))]
    exact E.retention.right_inverse (interior_subset
      (policy.compact_post_component_subset_interior hC hlow hz))
  · exact E.retention.map_smooth.comp
      (E.limit_identify.inverse_smooth.mono (Set.subset_univ _)) (fun _ hz => hD (hG hz))
  · exact E.limit_identify.map_smooth.comp
      (E.retention.inverse_smooth.mono
        ((policy.compact_post_component_subset_interior hC hlow).trans interior_subset))
      (fun _ hz => E.retained_pre_subset (hD (hB hz)))

theorem SurgeryEventTerminalPolicy.compact_component_metric
    (policy : SurgeryEventTerminalPolicy E)
    {x : E.terminal.carrier} (hC : IsCompact (connectedComponent x))
    (hlow : ∃ y ∈ connectedComponent x,
      E.limit_connection.scalarCurvature y ≤ (P.delta T * P.r T)⁻¹ ^ 2)
    (z : E.terminal.carrier) (hz : z ∈ connectedComponent x)
    (v w : TangentSpace (𝓡 3) z) :
    (metric T).inner (E.retention.map (E.limit_identify.inverse z))
      (mfderiv (𝓡 3) (𝓡 3) (E.retention.map ∘ E.limit_identify.inverse) z v)
      (mfderiv (𝓡 3) (𝓡 3) (E.retention.map ∘ E.limit_identify.inverse) z w) =
        E.limit_metric.inner z v w := by
  have hzD := (E.limit_inverse_image_component hC).subset ⟨z, hz, rfl⟩
  have hzint := policy.compact_pre_component_subset_interior hC hlow hzD
  have hzret := interior_subset hzint
  have hzU := E.retained_pre_subset hzret
  have hg : MDifferentiableAt (𝓡 3) (𝓡 3) E.limit_identify.inverse z :=
    (contMDiffOn_univ.1 E.limit_identify.inverse_smooth).mdifferentiable (by simp) z
  have hf : MDifferentiableAt (𝓡 3) (𝓡 3) E.limit_identify.map
      (E.limit_identify.inverse z) :=
    (E.limit_identify.map_smooth.contMDiffAt
      (E.regular_limit_open.mem_nhds hzU)).mdifferentiableAt (by simp)
  have ha : MDifferentiableAt (𝓡 3) (𝓡 3) E.retention.map
      (E.limit_identify.inverse z) :=
    (E.retention.map_smooth.contMDiffAt (mem_interior_iff_mem_nhds.1 hzint)).mdifferentiableAt
      (by simp)
  have hcomp : E.limit_identify.map ∘ E.limit_identify.inverse = id := by
    funext y
    exact E.limit_identify.right_inverse (Set.mem_univ y)
  have hd := mfderiv_comp z hf hg
  rw [hcomp, mfderiv_id] at hd
  have hv (q : TangentSpace (𝓡 3) z) :
      mfderiv (𝓡 3) (𝓡 3) E.limit_identify.map (E.limit_identify.inverse z)
        (mfderiv (𝓡 3) (𝓡 3) E.limit_identify.inverse z q) = q :=
    (congrArg (fun A => A q) hd).symm
  have he := E.retained_metric (E.limit_identify.inverse z) hzret
    (mfderiv (𝓡 3) (𝓡 3) E.limit_identify.inverse z v)
    (mfderiv (𝓡 3) (𝓡 3) E.limit_identify.inverse z w)
  rw [hv v, hv w, E.limit_identify.right_inverse (Set.mem_univ z)] at he
  simpa only [mfderiv_comp z ha hg, ContinuousLinearMap.comp_apply] using he

end PoincareConjecture
