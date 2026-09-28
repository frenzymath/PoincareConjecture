import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Chain.Truncation
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Complement









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

private theorem mem_closure_region_iff (N : EpsilonNeck g) {a b : ℝ}
    (hab : a < b) {x : M} (hx : x ∈ N.carrier) :
    x ∈ closure (N.region a b) ↔
      a ≤ (N.coordinate_inverse x).2 ∧ (N.coordinate_inverse x).2 ≤ b := by
  have himage : N.coordinatePartialHomeomorph.symm.IsImage
      (N.region a b) ((univ : Set UnitTwoSphere) ×ˢ Ioo a b) := by
    intro y hy
    change (N.coordinate_inverse y).1 ∈ univ ∧
      (N.coordinate_inverse y).2 ∈ Ioo a b ↔
        y ∈ N.carrier ∧ a < (N.coordinate_inverse y).2 ∧
          (N.coordinate_inverse y).2 < b
    simp only [mem_univ, true_and, mem_Ioo, show y ∈ N.carrier from hy]
  have h := himage.closure.apply_mem_iff hx
  change N.coordinate_inverse x ∈ closure ((univ : Set UnitTwoSphere) ×ˢ Ioo a b) ↔
    x ∈ closure (N.region a b) at h
  simpa only [closure_prod_eq, closure_univ, closure_Ioo hab.ne,
    mem_prod, mem_univ, true_and, mem_Icc] using h.symm



theorem closure_interior_eq_of_slice_frontier (N : EpsilonNeck g)
    {K : Set M} {t : ℝ} (hclosed : IsClosed K)
    (ht : t ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (hfront : frontier K = range (fun q : UnitTwoSphere => N.coordinate_map (q, t)))
    (hK : ∀ y ∈ N.carrier, y ∈ K ↔ (N.coordinate_inverse y).2 ≤ t) :
    closure (interior K) = K := by
  have hopen : IsOpen (N.region (-N.epsilon⁻¹) t) := by
    change IsOpen (N.carrier ∩
      (fun y => (N.coordinate_inverse y).2) ⁻¹' Ioo (-N.epsilon⁻¹) t)
    exact N.coordinate_inverse_smooth.continuousOn.snd.isOpen_inter_preimage
      N.carrier_open isOpen_Ioo
  have hlower : N.region (-N.epsilon⁻¹) t ⊆ interior K := by
    apply hopen.subset_interior_iff.mpr
    intro x hx
    exact (hK x hx.1).mpr hx.2.2.le
  apply Subset.antisymm
  · exact closure_minimal interior_subset hclosed
  · intro x hx
    by_cases hxi : x ∈ interior K
    · exact subset_closure hxi
    have hxf : x ∈ frontier K := ⟨subset_closure hx, hxi⟩
    rw [hfront] at hxf
    obtain ⟨q, rfl⟩ := hxf
    have hdom : (q, t) ∈ N.cylinderDomain := ⟨mem_univ _, ht⟩
    apply closure_mono hlower
    rw [mem_closure_region_iff N ht.1 (N.coordinate_map_mem hdom),
      N.coordinate_inverse_coordinate_map hdom]
    exact ⟨ht.1.le, le_rfl⟩



theorem isConnected_component_diff_of_height_sublevel (N : EpsilonNeck g)
    {K : Set M} {t : ℝ} {c : M} (hclosed : IsClosed K)
    (ht : t ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (hfront : frontier K ⊆ N.carrier)
    (hN : N.carrier ⊆ connectedComponent c)
    (hne : (K ∩ connectedComponent c).Nonempty)
    (hK : ∀ y ∈ N.carrier, y ∈ K ↔ (N.coordinate_inverse y).2 ≤ t) :
    IsConnected (connectedComponent c \ K) := by
  have hcollar : Kᶜ ∩ N.carrier = N.region t N.epsilon⁻¹ := by
    ext x
    constructor
    · rintro ⟨hxK, hxN⟩
      refine ⟨hxN, ?_, (N.coordinate_inverse_mem x hxN).2.2⟩
      exact lt_of_not_ge (fun h => hxK ((hK x hxN).mpr h))
    · intro hx
      exact ⟨fun hk => (not_lt_of_ge ((hK x hx.1).mp hk)) hx.2.1, hx.1⟩
  have hcollarconn : IsConnected (Kᶜ ∩ N.carrier) := by
    rw [hcollar]
    exact N.isConnected_region ht.1.le le_rfl ht.2
  let : LocallyConnectedSpace M :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) M
  let V := connectedComponent c
  have hV : IsOpen V := isOpen_connectedComponent
  let : LocallyConnectedSpace V := hV.locallyConnectedSpace
  let : ConnectedSpace V := isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  let A : Set V := Subtype.val ⁻¹' Kᶜ
  let U : Set V := Subtype.val ⁻¹' N.carrier
  have hA : IsOpen A := hclosed.isOpen_compl.preimage continuous_subtype_val
  have hU : IsOpen U := N.carrier_open.preimage continuous_subtype_val
  have hImage : Subtype.val '' (A ∩ U) = Kᶜ ∩ N.carrier := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hN hx.2⟩, hx, rfl⟩
  have hAU : IsConnected (A ∩ U) := by
    refine ⟨?_, ?_⟩
    · have hn := hcollarconn.nonempty
      rw [← hImage] at hn
      exact hn.of_image
    · apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
      rw [hImage]
      exact hcollarconn.isPreconnected
  have hfrontA : frontier A ⊆ U := by
    intro x hx
    apply hfront
    rw [← frontier_compl]
    exact continuous_subtype_val.frontier_preimage_subset Kᶜ hx
  have hneA : A ≠ univ := by
    intro h
    obtain ⟨x, hxK, hxV⟩ := hne
    have hx : (⟨x, hxV⟩ : V) ∈ A := h ▸ mem_univ _
    exact hx hxK
  have hconn := Poincare.Topology.isConnected_of_inter_of_frontier_subset
    hA hU hAU hfrontA hneA
  have hImageA : Subtype.val '' A = V \ K := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, hy⟩
    · intro hx
      exact ⟨⟨x, hx.1⟩, hx.2, rfl⟩
  rw [← hImageA]
  exact hconn.image _ continuous_subtype_val.continuousOn

end PoincareConjecture.EpsilonNeck

namespace PoincareConjecture.CapCertificate



theorem exists_finite_chain_complement_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ C : CapCertificate g, C.epsilon ≤ ε₀ →
        ∀ (H : ConnectedNeckCapCover g) (T : BalancedNeckChain g C.epsilon),
          C.IsOutgoingChain H T →
          ∀ b : ℤ, T.shape = .finite 0 b →
          ∀ t : ℝ, t ∈ Ioo (C.epsilon⁻¹ / 2) C.epsilon⁻¹ →
            let K := (C.carrier ∪ (T.unionOpen : Set M)) \
              (T.neck b).region t C.epsilon⁻¹
            closure (interior K) = K ∧
              IsConnected (connectedComponent C.boundary_neck.center \ K) := by
  obtain ⟨ε₀, hε₀, hsmall, htrunc⟩ := exists_finite_chain_truncation_threshold.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g C hε H T hT b hshape t ht
  obtain ⟨hcompact, _, _, hfront, hcore, hconnected⟩ :=
    htrunc C hε H T hT b hshape t ht
  let K := (C.carrier ∪ (T.unionOpen : Set M)) \ (T.neck b).region t C.epsilon⁻¹
  have hzero : 0 ≤ b := by
    have h := hT.zero_active
    simpa only [hshape, ChainShape.active, mem_Icc, le_refl, true_and] using h
  have hb : b ∈ T.shape.active := by
    simpa only [hshape, ChainShape.active, mem_Icc] using And.intro hzero (le_refl b)
  have he := T.epsilon_eq b hb
  have hR : 0 < C.epsilon⁻¹ := inv_pos.mpr C.epsilon_pos
  have htN : t ∈ Ioo (-(T.neck b).epsilon⁻¹) (T.neck b).epsilon⁻¹ := by
    rw [he]
    exact ⟨by linarith [ht.1], ht.2⟩
  have hlocal : ∀ y ∈ (T.neck b).carrier,
      y ∈ K ↔ ((T.neck b).coordinate_inverse y).2 ≤ t := by
    intro y hy
    have hyA : y ∈ C.carrier ∪ (T.unionOpen : Set M) :=
      Or.inr (mem_iUnion.mpr ⟨⟨b, hb⟩, hy⟩)
    have hyt := ((T.neck b).coordinate_inverse_mem y hy).2.2
    rw [he] at hyt
    change (y ∈ C.carrier ∪ (T.unionOpen : Set M) ∧
      ¬ (y ∈ (T.neck b).carrier ∧ t < ((T.neck b).coordinate_inverse y).2 ∧
        ((T.neck b).coordinate_inverse y).2 < C.epsilon⁻¹)) ↔
      ((T.neck b).coordinate_inverse y).2 ≤ t
    simp only [hyA, hy, hyt, true_and, and_true, not_lt]
  have hregular := (T.neck b).closure_interior_eq_of_slice_frontier
    hcompact.isClosed htN hfront hlocal
  change closure (interior K) = K at hregular
  refine ⟨hregular, ?_⟩
  have hKconn : IsConnected K := hregular ▸ hconnected.closure
  obtain ⟨p, hp⟩ := C.core_nonempty
  have hpK : p ∈ K := interior_subset (hcore (C.core_subset_closed_core hp))
  have hpV := C.carrier_subset_boundary_component (C.core_subset_carrier hp)
  have hKV : K ⊆ connectedComponent C.boundary_neck.center := by
    have h := hKconn.subset_connectedComponent hpK
    rwa [← connectedComponent_eq hpV] at h
  have hfrontN : frontier K ⊆ (T.neck b).carrier := by
    rw [hfront]
    rintro _ ⟨q, rfl⟩
    exact (T.neck b).coordinate_map_mem ⟨mem_univ _, htN⟩
  have hNV : (T.neck b).carrier ⊆ connectedComponent C.boundary_neck.center := by
    obtain ⟨q⟩ := (inferInstance : Nonempty UnitTwoSphere)
    have hqN := (T.neck b).coordinate_map_mem (show (q, t) ∈ (T.neck b).cylinderDomain from
      ⟨mem_univ _, htN⟩)
    have hqK : (T.neck b).coordinate_map (q, t) ∈ K := by
      apply hcompact.isClosed.closure_eq ▸ frontier_subset_closure
      rw [hfront]
      exact mem_range_self q
    have h := (T.neck b).isConnected_carrier.subset_connectedComponent hqN
    rwa [← connectedComponent_eq (hKV hqK)] at h
  exact (T.neck b).isConnected_component_diff_of_height_sublevel
    hcompact.isClosed htN hfrontN hNV ⟨p, hpK, hpV⟩ hlocal

end PoincareConjecture.CapCertificate
