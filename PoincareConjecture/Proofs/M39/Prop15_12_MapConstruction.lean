import PoincareConjecture.Definitions.M39ComparisonMap
import PoincareConjecture.Proofs.M07.Geometry.Manifold.InverseFunction

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M39

section Retained

variable {g₀ : StandardInitialMetric} {D : RepairedSurgeryFlowData.{u} g₀}
  {T : ℝ} {hT : T ∈ D.flow.surgery_times}
  [Nonempty (D.flow.slice T).carrier]
  (I : RepairedComparisonMapInput D T hT)

noncomputable def retainedMap : I.parent.carrier.carrier → I.child.carrier.carrier :=
  fun x => I.child.inverse ((D.flow.event T hT).retention.map (I.parent.inclusion x))

theorem inclusion_retainedMap {x : I.parent.carrier.carrier} (hx : x ∈ I.retained) :
    I.child.inclusion (retainedMap I x) =
      (D.flow.event T hT).retention.map (I.parent.inclusion x) := by
  obtain ⟨y, hy⟩ := I.retained_to_child x hx
  rw [retainedMap, ← hy, I.child.left_inverse]

theorem retainedMap_injOn : Set.InjOn (retainedMap I) I.retained := by
  intro x hx y hy hxy
  apply I.parent.inclusion_openEmbedding.injective
  have heq := congrArg I.child.inclusion hxy
  rw [inclusion_retainedMap I hx, inclusion_retainedMap I hy] at heq
  have h := congrArg (D.flow.event T hT).retention.inverse heq
  rwa [(D.flow.event T hT).retention.left_inverse
      (interior_subset (I.retained_subset x hx)),
    (D.flow.event T hT).retention.left_inverse
      (interior_subset (I.retained_subset y hy))] at h

theorem retainedMap_smooth :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (retainedMap I) I.retained := by
  have hpre : I.retained ⊆
      interior (I.parent.inclusion ⁻¹' (D.flow.event T hT).retained_pre) := by
    apply interior_maximal
    · intro x hx
      change I.parent.inclusion x ∈ (D.flow.event T hT).retained_pre
      exact interior_subset (I.retained_subset x hx)
    · exact I.retained_open
  have hs : ContMDiffOn (𝓡 3) (𝓡 3) ∞
      ((D.flow.event T hT).retention.map ∘ I.parent.inclusion) I.retained :=
    (D.flow.event T hT).retention.map_smooth.comp
      (I.parent.inclusion_smooth.contMDiffOn (s := I.retained))
      (fun x hx => interior_subset (hpre hx))
  exact I.child.inverse_smooth.comp hs (fun x hx => I.retained_to_child x hx)

theorem retainedMap_metric (x : I.parent.carrier.carrier) (hx : x ∈ I.retained)
    (v w : TangentSpace (𝓡 3) x) :
    I.child_metric.inner (retainedMap I x)
      (mfderiv (𝓡 3) (𝓡 3) (retainedMap I) x v)
      (mfderiv (𝓡 3) (𝓡 3) (retainedMap I) x w) =
      (D.flow.event T hT).limit_metric.inner
        ((D.flow.event T hT).limit_identify.map (I.parent.inclusion x))
        (mfderiv (𝓡 3) (𝓡 3) (D.flow.event T hT).limit_identify.map
          (I.parent.inclusion x) (mfderiv (𝓡 3) (𝓡 3) I.parent.inclusion x v))
        (mfderiv (𝓡 3) (𝓡 3) (D.flow.event T hT).limit_identify.map
          (I.parent.inclusion x) (mfderiv (𝓡 3) (𝓡 3) I.parent.inclusion x w)) := by
  have hret := ((D.flow.event T hT).retention.map_smooth
    (I.parent.inclusion x) (interior_subset (I.retained_subset x hx))).contMDiffAt
      (mem_interior_iff_mem_nhds.mp (I.retained_subset x hx))
  have hmap := ((retainedMap_smooth I) x hx).contMDiffAt
    (I.retained_open.mem_nhds hx)
  have heq : (I.child.inclusion ∘ retainedMap I) =ᶠ[𝓝 x]
      ((D.flow.event T hT).retention.map ∘ I.parent.inclusion) := by
    filter_upwards [I.retained_open.mem_nhds hx] with y hy
    exact inclusion_retainedMap I hy
  have hd := heq.mfderiv_eq (I := 𝓡 3) (I' := 𝓡 3)
  rw [mfderiv_comp x (I.child.inclusion_smooth.mdifferentiable (by simp) _)
      (hmap.mdifferentiableAt (by simp)),
    mfderiv_comp x (hret.mdifferentiableAt (by simp))
      (I.parent.inclusion_smooth.mdifferentiable (by simp) _)] at hd
  have hv := congrArg (fun L => L v) hd
  have hw := congrArg (fun L => L w) hd
  simp only [ContinuousLinearMap.comp_apply] at hv hw
  erw [← I.child_pullback, inclusion_retainedMap I hx, hv, hw]
  exact (D.flow.event T hT).retained_metric (I.parent.inclusion x)
    (interior_subset (I.retained_subset x hx)) _ _

theorem eqOn_retainedMap
    {f : I.parent.carrier.carrier → I.child.carrier.carrier}
    (hf : ∀ x ∈ I.retained, I.child.inclusion (f x) =
      (D.flow.event T hT).retention.map (I.parent.inclusion x)) :
    Set.EqOn f (retainedMap I) I.retained := by
  intro x hx
  exact I.child.inclusion_openEmbedding.injective
    ((hf x hx).trans (inclusion_retainedMap I hx).symm)

theorem extension_retained_smooth
    {f : I.parent.carrier.carrier → I.child.carrier.carrier}
    (hf : ∀ x ∈ I.retained, I.child.inclusion (f x) =
      (D.flow.event T hT).retention.map (I.parent.inclusion x)) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ f I.retained := by
  exact (retainedMap_smooth I).congr (eqOn_retainedMap I hf)

end Retained

section Local

variable {g₀ : StandardInitialMetric} {K : MetricSurgeryConstants}
  {P : SurgeryParameters} {slice : ℝ → GeneralizedSliceCarrier.{u}}
  {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {T : ℝ}
  (E : SurgeryEventData g₀ K P slice metric T)

theorem retention_map_mem_post {x : (slice E.tMinus).carrier}
    (hx : x ∈ E.retained_pre) : E.retention.map x ∈ E.retained_post := by
  have h : E.retention.map x ∈ E.retention.map '' E.retained_pre :=
    ⟨x, hx, rfl⟩
  rwa [E.retention.map_image] at h

theorem retention_inverse_mem_pre {y : (slice T).carrier}
    (hy : y ∈ E.retained_post) : E.retention.inverse y ∈ E.retained_pre := by
  have h : E.retention.inverse y ∈ E.retention.inverse '' E.retained_post :=
    ⟨y, hy, rfl⟩
  rwa [E.retention.inverse_image] at h

noncomputable def retainedHomeomorph : E.retained_pre ≃ₜ E.retained_post where
  toFun x := ⟨E.retention.map x,
    retention_map_mem_post E x.property⟩
  invFun y := ⟨E.retention.inverse y,
    retention_inverse_mem_pre E y.property⟩
  left_inv x := Subtype.ext (E.retention.left_inverse x.property)
  right_inv y := Subtype.ext (E.retention.right_inverse y.property)
  continuous_toFun := E.retention.map_smooth.continuousOn.domRestrict.subtype_mk _
  continuous_invFun := E.retention.inverse_smooth.continuousOn.domRestrict.subtype_mk _

theorem preSphere_subset_retained (i : Fin E.cap_count) :
    E.limit_identify.inverse '' (E.necks i).neck.central_sphere ⊆ E.retained_pre := by
  intro x hx
  apply E.retained_pre_compact.isClosed.frontier_subset
  rw [E.pre_boundary]
  exact Set.mem_iUnion.mpr ⟨i, hx⟩

theorem neckCentralSphere_isConnected (i : Fin E.cap_count) :
    IsConnected (E.necks i).neck.central_sphere := by
  let N := (E.necks i).neck
  have hpos : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  let zeroHeight : Set.Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    ⟨0, neg_lt_zero.mpr hpos, hpos⟩
  let f : UnitTwoSphere → E.terminal.carrier :=
    fun theta => (N.coordinate (theta, zeroHeight)).val
  have hf : Continuous f := continuous_subtype_val.comp
    (N.coordinate.continuous.comp (continuous_id.prodMk continuous_const))
  haveI : ConnectedSpace UnitTwoSphere := Subtype.connectedSpace
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp))
      (0 : EuclideanSpace ℝ (Fin 3)) zero_le_one)
  have hset : Set.range f = N.central_sphere := by
    rw [N.central_sphere_eq]
    ext x
    constructor
    · rintro ⟨theta, rfl⟩
      exact ⟨(theta, 0), ⟨Set.mem_univ _, rfl⟩,
        (N.coordinate_map_eq (theta, zeroHeight)).symm⟩
    · rintro ⟨⟨theta, s⟩, hs, himage⟩
      have hs0 : s = 0 := hs.2
      subst s
      exact ⟨theta, (N.coordinate_map_eq (theta, zeroHeight)).trans himage⟩
  rw [← hset]
  exact isConnected_range hf

theorem preSphere_isConnected (i : Fin E.cap_count) :
    IsConnected (E.limit_identify.inverse '' (E.necks i).neck.central_sphere) := by
  exact (neckCentralSphere_isConnected E i).image E.limit_identify.inverse
    (E.limit_identify.inverse_smooth.continuousOn.mono (Set.subset_univ _))

theorem neckCentralSphere_isCompact (i : Fin E.cap_count) :
    IsCompact (E.necks i).neck.central_sphere := by
  let N := (E.necks i).neck
  have hpos : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  rw [N.central_sphere_eq]
  apply (isCompact_univ.prod (isCompact_singleton (x := (0 : ℝ)))).image_of_continuousOn
  apply N.coordinate_map_smooth.continuousOn.mono
  intro z hz
  have hs : z.2 = 0 := hz.2
  exact ⟨hz.1, hs ▸ ⟨neg_lt_zero.mpr hpos, hpos⟩⟩

theorem preSphere_isCompact (i : Fin E.cap_count) :
    IsCompact (E.limit_identify.inverse '' (E.necks i).neck.central_sphere) := by
  exact (neckCentralSphere_isCompact E i).image_of_continuousOn
    (E.limit_identify.inverse_smooth.continuousOn.mono (Set.subset_univ _))

theorem preSphere_subset_parent (i : Fin E.cap_count)
    (C : SurgerySelectedComponent (slice E.tMinus))
    (hmeet : (C.inclusion ⁻¹'
      (E.limit_identify.inverse '' (E.necks i).neck.central_sphere)).Nonempty) :
    E.limit_identify.inverse '' (E.necks i).neck.central_sphere ⊆
      Set.range C.inclusion := by
  obtain ⟨x, hx⟩ := hmeet
  have hsub := (preSphere_isConnected E i).subset_connectedComponent hx
  have hC : C.inclusion x ∈ connectedComponent (C.inclusion C.basepoint) := by
    rw [← C.range_eq_component]
    exact Set.mem_range_self x
  rw [C.range_eq_component, connectedComponent_eq hC]
  exact hsub

theorem parentSphere_isConnected (i : Fin E.cap_count)
    (C : SurgerySelectedComponent (slice E.tMinus))
    (hmeet : (C.inclusion ⁻¹'
      (E.limit_identify.inverse '' (E.necks i).neck.central_sphere)).Nonempty) :
    IsConnected (C.inclusion ⁻¹'
      (E.limit_identify.inverse '' (E.necks i).neck.central_sphere)) := by
  exact (preSphere_isConnected E i).preimage_of_isOpenMap
    C.inclusion_openEmbedding.injective C.inclusion_openEmbedding.isOpenMap
    (preSphere_subset_parent E i C hmeet)

theorem parentSphere_isClosed (i : Fin E.cap_count)
    (C : SurgerySelectedComponent (slice E.tMinus)) :
    IsClosed (C.inclusion ⁻¹'
      (E.limit_identify.inverse '' (E.necks i).neck.central_sphere)) :=
  (preSphere_isCompact E i).isClosed.preimage C.inclusion_openEmbedding.continuous

theorem cap_frontier_isConnected (i : Fin E.cap_count) :
    IsConnected (frontier (E.caps i).carrier) := by
  rw [← E.boundary_correspondence i]
  exact (preSphere_isConnected E i).image E.retention.map
    (E.retention.map_smooth.continuousOn.mono (preSphere_subset_retained E i))

theorem retention_mem_cap_iff (i : Fin E.cap_count)
    {x : (slice E.tMinus).carrier} (hx : x ∈ E.retained_pre) :
    E.retention.map x ∈ (E.caps i).carrier ↔
      x ∈ E.limit_identify.inverse '' (E.necks i).neck.central_sphere := by
  constructor
  · intro hcap
    have hpost : E.retention.map x ∈ E.retained_post :=
      retention_map_mem_post E hx
    have hboundary : E.retention.map x ∈ frontier (E.caps i).carrier := by
      rw [← E.cap_boundary i]
      exact ⟨hpost, hcap⟩
    rw [← E.boundary_correspondence i] at hboundary
    obtain ⟨y, hy, hyx⟩ := hboundary
    have heq := congrArg E.retention.inverse hyx
    rw [E.retention.left_inverse (preSphere_subset_retained E i hy),
      E.retention.left_inverse hx] at heq
    exact heq ▸ hy
  · intro hsphere
    apply (E.caps i).carrier_compact.isClosed.frontier_subset
    rw [← E.boundary_correspondence i]
    exact ⟨x, hsphere, rfl⟩

theorem mem_retainedInterior_iff (x : (slice E.tMinus).carrier)
    (hx : x ∈ E.retained_pre) :
    x ∈ interior E.retained_pre ↔ ∀ i, E.retention.map x ∉ (E.caps i).carrier := by
  constructor
  · intro hi i hcap
    have hboundary : x ∈ frontier E.retained_pre := by
      rw [E.pre_boundary]
      exact Set.mem_iUnion.mpr ⟨i, (retention_mem_cap_iff E i hx).mp hcap⟩
    exact (mem_frontier_iff_notMem_interior hx).mp hboundary hi
  · intro hcaps
    by_contra hi
    have hboundary := (mem_frontier_iff_notMem_interior hx).mpr hi
    rw [E.pre_boundary] at hboundary
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hboundary
    exact hcaps i ((retention_mem_cap_iff E i hx).mpr hi)

theorem retention_image_interior :
    E.retention.map '' interior E.retained_pre =
      E.retained_post \ ⋃ i, (E.caps i).carrier := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨?_, ?_⟩
    · exact retention_map_mem_post E (interior_subset hx)
    · intro hcap
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hcap
      exact (mem_retainedInterior_iff E x (interior_subset hx)).mp hx i hi
  · rintro ⟨hy, hcaps⟩
    obtain ⟨x, hx, rfl⟩ := E.retention.map_image.symm ▸ hy
    refine ⟨x, (mem_retainedInterior_iff E x hx).mpr ?_, rfl⟩
    intro i hi
    exact hcaps (Set.mem_iUnion.mpr ⟨i, hi⟩)

theorem retention_mfderiv_bijective {x : (slice E.tMinus).carrier}
    (hx : x ∈ interior E.retained_pre) :
    Function.Bijective (mfderiv (𝓡 3) (𝓡 3) E.retention.map x) := by
  have hmaps : Set.MapsTo E.retention.map (interior E.retained_pre) E.retained_post := by
    intro y hy
    exact retention_map_mem_post E (interior_subset hy)
  have hf := ((E.retention.map_smooth x (interior_subset hx)).contMDiffAt
    (mem_interior_iff_mem_nhds.mp hx)).mdifferentiableAt (by simp)
  have hg := (E.retention.inverse_smooth _ (hmaps hx)).mdifferentiableWithinAt (by simp)
  have hc := (hg.hasMFDerivWithinAt.comp x
    (hf.hasMFDerivAt.hasMFDerivWithinAt (s := interior E.retained_pre)) hmaps).hasMFDerivAt
      (isOpen_interior.mem_nhds hx)
  have heq : E.retention.inverse ∘ E.retention.map =ᶠ[𝓝 x] id := by
    filter_upwards [isOpen_interior.mem_nhds hx] with y hy
    exact E.retention.left_inverse (interior_subset hy)
  have hd := hc.mfderiv
  rw [heq.mfderiv_eq (I := 𝓡 3) (I' := 𝓡 3), mfderiv_id] at hd
  have hinj : Function.Injective (mfderiv (𝓡 3) (𝓡 3) E.retention.map x) := by
    intro v w hvw
    have hv := congrArg (fun L => L v) hd
    have hw := congrArg (fun L => L w) hd
    simp only [ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply] at hv hw
    exact hv.trans ((congrArg _ hvw).trans hw.symm)
  letI : FiniteDimensional ℝ (TangentSpace (𝓡 3) x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : (slice E.tMinus).carrier → Type _) x
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (mfderiv (𝓡 3) (𝓡 3) E.retention.map x).toLinearMap) rfl).mp hinj⟩

theorem retention_image_isOpen {U : Set (slice E.tMinus).carrier}
    (hU : IsOpen U) (hsub : U ⊆ interior E.retained_pre) :
    IsOpen (E.retention.map '' U) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro _ ⟨x, hx, rfl⟩
  have hs := (E.retention.map_smooth x (interior_subset (hsub hx))).contMDiffAt
    (mem_interior_iff_mem_nhds.mp (hsub hx))
  rw [← Poincare.map_nhds_eq_of_contMDiffAt_mfderiv_bijective hs
    (retention_mfderiv_bijective E (hsub hx))]
  exact Filter.image_mem_map (hU.mem_nhds hx)

noncomputable def localComparison (i : Fin E.cap_count) :
    (slice E.tMinus).carrier → (slice T).carrier :=
  fun x => E.local_embed i ((E.local_result i).collapse (E.limit_identify.map x))

theorem localComparison_continuousOn (i : Fin E.cap_count) :
    ContinuousOn (localComparison E i)
      (E.regular_limit ∩ E.limit_identify.map ⁻¹' (E.necks i).neck.carrier) := by
  exact (E.local_embed_smooth i).continuous.comp_continuousOn
    ((E.local_result i).collapse_continuous.comp
      (E.limit_identify.map_smooth.continuousOn.mono Set.inter_subset_left)
      (fun _ hx => hx.2))

theorem localComparison_eq_retention (i : Fin E.cap_count)
    {x : (slice E.tMinus).carrier} (hx : x ∈ E.regular_limit)
    (hn : E.limit_identify.map x ∈
      (E.necks i).neck.region (-(E.necks i).neck.epsilon⁻¹) 0) :
    localComparison E i x = E.retention.map x := by
  exact (E.local_retention i _ hn).trans
    (congrArg E.retention.map (E.limit_identify.left_inverse hx))

theorem localComparison_positive_mem_cap (i : Fin E.cap_count)
    {x : (slice E.tMinus).carrier}
    (hx : E.limit_identify.map x ∈
      (E.necks i).neck.region 0 (E.necks i).neck.epsilon⁻¹) :
    localComparison E i x ∈ (E.caps i).carrier := by
  rw [← E.local_cap_image i]
  exact ⟨_, (E.local_result i).collapse_positive_cap ⟨_, hx, rfl⟩, rfl⟩

theorem localComparison_central_mem_cap (i : Fin E.cap_count)
    {x : (slice E.tMinus).carrier}
    (hx : E.limit_identify.map x ∈ (E.necks i).neck.central_sphere) :
    localComparison E i x ∈ (E.caps i).carrier := by
  rw [← E.local_cap_image i]
  refine ⟨_, frontier_subset_closure ?_, rfl⟩
  rw [← (E.local_result i).cap_boundary]
  exact ⟨_, hx, rfl⟩

theorem localComparison_constant_tail (i : Fin E.cap_count) :
    ∃ b : ℝ, 0 < b ∧ b < (E.necks i).neck.epsilon⁻¹ ∧
      ∀ x : (slice E.tMinus).carrier,
        E.limit_identify.map x ∈ (E.necks i).neck.carrier →
        b ≤ ((E.necks i).neck.coordinate_inverse (E.limit_identify.map x)).2 →
        localComparison E i x = (E.caps i).tip := by
  obtain ⟨b, hb, hbell, htail⟩ := (E.local_result i).collapse_positive_tail
  refine ⟨b, hb, hbell, fun x hx hs => ?_⟩
  dsimp only [localComparison]
  rw [htail _ hx hs, E.local_tip]

theorem local_embed_range_subset_child (i : Fin E.cap_count)
    (C : SurgerySelectedComponent (slice T))
    (hmeet : ∃ z, E.local_embed i z ∈ Set.range C.inclusion) :
    Set.range (E.local_embed i) ⊆ Set.range C.inclusion := by
  obtain ⟨e⟩ := (E.local_result i).open_ball_model
  haveI : ConnectedSpace (ULift.{u} StandardCapSpace) :=
    (Homeomorph.ulift : ULift.{u} StandardCapSpace ≃ₜ StandardCapSpace).connectedSpace_iff.mpr
      inferInstance
  haveI : ConnectedSpace (E.local_result i).output.carrier :=
    e.connectedSpace_iff.mpr inferInstance
  obtain ⟨z, hz⟩ := hmeet
  have hsub := (isConnected_range (E.local_embed_smooth i).continuous).subset_connectedComponent
    (Set.mem_range_self z)
  rw [C.range_eq_component] at hz ⊢
  exact hsub.trans (by rw [connectedComponent_eq hz])

theorem local_embed_range_subset_child_of_negative (i : Fin E.cap_count)
    (C : SurgerySelectedComponent (slice T))
    {z : E.terminal.carrier}
    (hz : z ∈ (E.necks i).neck.region (-(E.necks i).neck.epsilon⁻¹) 0)
    (hc : E.retention.map (E.limit_identify.inverse z) ∈ Set.range C.inclusion) :
    Set.range (E.local_embed i) ⊆ Set.range C.inclusion := by
  apply local_embed_range_subset_child E i C
  exact ⟨(E.local_result i).collapse z, (E.local_retention i z hz).symm ▸ hc⟩

theorem cap_subset_child (i : Fin E.cap_count)
    (C : SurgerySelectedComponent (slice T))
    (hC : Set.range (E.local_embed i) ⊆ Set.range C.inclusion) :
    (E.caps i).carrier ⊆ Set.range C.inclusion := by
  rw [← E.local_cap_image i]
  exact (Set.image_subset_range _ _).trans hC

theorem cap_tip_mem_child (i : Fin E.cap_count)
    (C : SurgerySelectedComponent (slice T))
    (hC : Set.range (E.local_embed i) ⊆ Set.range C.inclusion) :
    (E.caps i).tip ∈ Set.range C.inclusion := by
  rw [← E.local_tip i]
  exact hC (Set.mem_range_self _)

noncomputable def localChildComparison (i : Fin E.cap_count)
    (C : SurgerySelectedComponent (slice T)) :
    (slice E.tMinus).carrier → C.carrier.carrier :=
  C.inverse ∘ localComparison E i

theorem inclusion_localChildComparison (i : Fin E.cap_count)
    (C : SurgerySelectedComponent (slice T))
    (hC : Set.range (E.local_embed i) ⊆ Set.range C.inclusion)
    (x : (slice E.tMinus).carrier) :
    C.inclusion (localChildComparison E i C x) = localComparison E i x := by
  obtain ⟨y, hy⟩ := hC (Set.mem_range_self
    ((E.local_result i).collapse (E.limit_identify.map x)))
  change C.inclusion (C.inverse (localComparison E i x)) = localComparison E i x
  change C.inclusion y = localComparison E i x at hy
  rw [← hy, C.left_inverse]

theorem localChildComparison_continuousOn (i : Fin E.cap_count)
    (C : SurgerySelectedComponent (slice T))
    (hC : Set.range (E.local_embed i) ⊆ Set.range C.inclusion) :
    ContinuousOn (localChildComparison E i C)
      (E.regular_limit ∩ E.limit_identify.map ⁻¹' (E.necks i).neck.carrier) := by
  apply C.inverse_smooth.continuousOn.comp (localComparison_continuousOn E i)
  intro x _
  exact hC (Set.mem_range_self _)

theorem localChildComparison_eq_retention (i : Fin E.cap_count)
    (C : SurgerySelectedComponent (slice T))
    {x : (slice E.tMinus).carrier} (hx : x ∈ E.regular_limit)
    (hn : E.limit_identify.map x ∈
      (E.necks i).neck.region (-(E.necks i).neck.epsilon⁻¹) 0) :
    localChildComparison E i C x = C.inverse (E.retention.map x) :=
  congrArg C.inverse (localComparison_eq_retention E i hx hn)

theorem localChildComparison_constant_tail (i : Fin E.cap_count)
    (C : SurgerySelectedComponent (slice T)) :
    ∃ b : ℝ, 0 < b ∧ b < (E.necks i).neck.epsilon⁻¹ ∧
      ∀ x : (slice E.tMinus).carrier,
        E.limit_identify.map x ∈ (E.necks i).neck.carrier →
        b ≤ ((E.necks i).neck.coordinate_inverse (E.limit_identify.map x)).2 →
        localChildComparison E i C x = C.inverse (E.caps i).tip := by
  obtain ⟨b, hb, hell, htail⟩ := localComparison_constant_tail E i
  exact ⟨b, hb, hell, fun x hx hs => congrArg C.inverse (htail x hx hs)⟩

end Local

section Extension

variable {g₀ : StandardInitialMetric} {D : RepairedSurgeryFlowData.{u} g₀}
  {T : ℝ} {hT : T ∈ D.flow.surgery_times}
  [Nonempty (D.flow.slice T).carrier]
  (I : RepairedComparisonMapInput D T hT)

theorem retainedMap_target_open :
    IsOpen (I.child.inclusion '' retainedMap I '' I.retained) := by
  rw [Set.image_image]
  have heq : Set.EqOn (I.child.inclusion ∘ retainedMap I)
      ((D.flow.event T hT).retention.map ∘ I.parent.inclusion) I.retained :=
    fun _ hx => inclusion_retainedMap I hx
  change IsOpen ((I.child.inclusion ∘ retainedMap I) '' I.retained)
  rw [heq.image_eq, Set.image_comp]
  apply retention_image_isOpen (D.flow.event T hT)
    (I.parent.inclusion_openEmbedding.isOpenMap _ I.retained_open)
  rintro _ ⟨x, hx, rfl⟩
  exact I.retained_subset x hx

theorem extension_retained_target_open
    {f : I.parent.carrier.carrier → I.child.carrier.carrier}
    (hf : ∀ x ∈ I.retained, I.child.inclusion (f x) =
      (D.flow.event T hT).retention.map (I.parent.inclusion x)) :
    IsOpen (I.child.inclusion '' f '' I.retained) := by
  rw [(eqOn_retainedMap I hf).image_eq]
  exact retainedMap_target_open I

theorem extension_retained_metric
    {f : I.parent.carrier.carrier → I.child.carrier.carrier}
    (hf : ∀ x ∈ I.retained, I.child.inclusion (f x) =
      (D.flow.event T hT).retention.map (I.parent.inclusion x))
    (x : I.parent.carrier.carrier) (hx : x ∈ I.retained)
    (v w : TangentSpace (𝓡 3) x) :
    I.child_metric.inner (f x)
      (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x w) =
      (D.flow.event T hT).limit_metric.inner
        ((D.flow.event T hT).limit_identify.map (I.parent.inclusion x))
        (mfderiv (𝓡 3) (𝓡 3) (D.flow.event T hT).limit_identify.map
          (I.parent.inclusion x) (mfderiv (𝓡 3) (𝓡 3) I.parent.inclusion x v))
        (mfderiv (𝓡 3) (𝓡 3) (D.flow.event T hT).limit_identify.map
          (I.parent.inclusion x) (mfderiv (𝓡 3) (𝓡 3) I.parent.inclusion x w)) := by
  have heq : f =ᶠ[𝓝 x] retainedMap I := by
    filter_upwards [I.retained_open.mem_nhds hx] with y hy
    exact eqOn_retainedMap I hf hy
  rw [heq.eq_of_nhds, heq.mfderiv_eq (I := 𝓡 3) (I' := 𝓡 3)]
  exact retainedMap_metric I x hx v w

end Extension

end PoincareConjecture.M39
