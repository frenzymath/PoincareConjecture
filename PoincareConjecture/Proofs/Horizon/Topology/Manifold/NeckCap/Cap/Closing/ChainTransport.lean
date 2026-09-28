import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Closing.ChainBoundary
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Closing.CoreExpansion
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Chain.Truncation
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Attachment.ChainIntersection
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Overlap.SliceProjection












set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}


theorem graphTransport_closed_core_subset_of_graph_in_core (D : CapCertificate g)
    {r : ℝ} (hr : 0 < r) (hrB : r < D.boundary_neck.epsilon⁻¹)
    (h : UnitTwoSphere → ℝ) (hh : Continuous h) (hbound : ∀ q, |h q| < r)
    (hcore : ∀ q, D.boundary_neck.coordinate_map (q, h q) ∈ D.core) :
    D.boundary_neck.graphTransport hr hrB h hh hbound '' D.closed_core ⊆ D.closed_core := by
  let B := D.boundary_neck
  let e := B.graphTransport hr hrB h hh hbound
  have hcoreImage : e '' D.core ⊆ D.core := by
    rintro _ ⟨y, hy, rfl⟩
    by_cases hyB : y ∈ B.carrier
    · let q := (B.coordinate_inverse y).1
      let t := (B.coordinate_inverse y).2
      have hdom := B.coordinate_inverse_mem y hyB
      have hhdom : (q, h q) ∈ B.cylinderDomain :=
        ⟨mem_univ _, abs_lt.mp ((hbound q).trans hrB)⟩
      have hz : (q, t) ∈ B.cylinderDomain := hdom
      have hmove : Homeomorph.Vertical.move r (h q) t ∈ Ioo (-B.epsilon⁻¹) B.epsilon⁻¹ :=
        (Homeomorph.Vertical.move_mem_Ioo_iff hr hrB.le (hbound q)).mpr hz.2
      have hmap : e y = B.coordinate_map (q, Homeomorph.Vertical.move r (h q) t) := by
        rw [← B.coordinate_map_coordinate_inverse hyB]
        exact B.graphTransport_apply hr hrB h hh hbound hdom
      have hnew : B.coordinate_map (q, Homeomorph.Vertical.move r (h q) t) ∈ B.carrier :=
        B.coordinate_map_mem ⟨mem_univ _, hmove⟩
      have hheight : (B.coordinate_inverse
          (B.coordinate_map (q, Homeomorph.Vertical.move r (h q) t))).2 =
          Homeomorph.Vertical.move r (h q) t :=
        congrArg Prod.snd (B.coordinate_inverse_coordinate_map ⟨mem_univ _, hmove⟩)
      rcases D.boundary_neck_sides with ⟨hn, hp⟩ | ⟨hp, hn⟩
      · have hnegative {x : M} (hx : x ∈ D.core) (hxB : x ∈ B.carrier) :
            x ∈ B.region (-B.epsilon⁻¹) 0 := by
          rcases B.carrier_subset_region_union_central_union_region hxB with
            (hneg | hsphere) | hpos
          · exact hneg
          · exact (disjoint_left.mp D.disjoint_core_boundary hx
              (D.boundary_eq_neck_sphere.symm ▸ hsphere)).elim
          · exact (disjoint_left.mp D.disjoint_closed_core_end
              (D.core_subset_closed_core hx) (hp hpos)).elim
        have ht : t < 0 := (hnegative hy hyB).2.2
        have hhneg : h q < 0 := by
          have hi := (hnegative (hcore q) (B.coordinate_map_mem hhdom)).2.2
          rwa [B.coordinate_inverse_coordinate_map hhdom] at hi
        have hm := Homeomorph.Vertical.strictMono_move hr (hbound q) ht
        rw [Homeomorph.Vertical.move_zero hr] at hm
        rw [hmap]
        apply hn
        exact ⟨hnew, by rw [hheight]; exact ⟨hmove.1, hm.trans hhneg⟩⟩
      · have hpositive {x : M} (hx : x ∈ D.core) (hxB : x ∈ B.carrier) :
            x ∈ B.region 0 B.epsilon⁻¹ := by
          rcases B.carrier_subset_region_union_central_union_region hxB with
            (hneg | hsphere) | hpos
          · exact (disjoint_left.mp D.disjoint_closed_core_end
              (D.core_subset_closed_core hx) (hn hneg)).elim
          · exact (disjoint_left.mp D.disjoint_core_boundary hx
              (D.boundary_eq_neck_sphere.symm ▸ hsphere)).elim
          · exact hpos
        have ht : 0 < t := (hpositive hy hyB).2.1
        have hhpos : 0 < h q := by
          have hi := (hpositive (hcore q) (B.coordinate_map_mem hhdom)).2.1
          rwa [B.coordinate_inverse_coordinate_map hhdom] at hi
        have hm := Homeomorph.Vertical.strictMono_move hr (hbound q) ht
        rw [Homeomorph.Vertical.move_zero hr] at hm
        rw [hmap]
        apply hp
        exact ⟨hnew, by rw [hheight]; exact ⟨hhpos.trans hm, hmove.2⟩⟩
    · have hfix : e y = y := B.graphTransport_fixed hr hrB h hh hbound
        (fun hc => hyB (B.closedCollar_subset_carrier hrB hc))
      rwa [hfix]
  simpa only [D.closure_core_eq_closed_core, ← e.image_closure] using closure_mono hcoreImage

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] in
private theorem connected_subset_open_of_disjoint_frontier {S U : Set M}
    (hS : IsConnected S) (hU : IsOpen U) (hmeet : (U ∩ S).Nonempty)
    (hdis : Disjoint S (frontier U)) : S ⊆ U := by
  let : ConnectedSpace S := isConnected_iff_connectedSpace.mp hS
  have hclopen := isClopen_preimage_val hU hdis.symm
  obtain ⟨x, hxU, hxS⟩ := hmeet
  have hfull := hclopen.eq_univ ⟨⟨x, hxS⟩, hxU⟩
  intro y hy
  exact (show (⟨y, hy⟩ : S) ∈ Subtype.val ⁻¹' U from hfull ▸ mem_univ _)

private theorem contact_of_shrinking_transport_of_aligned_compact_region
    (C D : CapCertificate g) {A K : Set M} (hA : IsConnected A) (hAopen : IsOpen A)
    (hK : IsCompact K) (hKA : K ⊆ A) (hKconn : IsConnected (interior K))
    (hC : C.closed_core ⊆ interior K) (e : M ≃ₜ M)
    (hboundary : frontier K = e '' D.boundary_sphere)
    (hcarrier : e '' D.carrier = D.carrier)
    (hshrink : e '' D.closed_core ⊆ D.closed_core)
    (hdis : Disjoint D.closed_core C.carrier)
    (hcontact : (frontier A ∩ D.core).Nonempty) :
    (frontier A ∩ (e '' D.closed_core)).Nonempty := by
  have hecomponent : e '' connectedComponent D.boundary_neck.center =
      connectedComponent (e D.boundary_neck.center) := by
    have hi := e.image_connectedComponentIn (s := univ)
      (x := D.boundary_neck.center) (mem_univ _)
    simpa only [image_univ, e.surjective.range_eq, connectedComponentIn_univ] using hi
  have hcenter : e D.boundary_neck.center ∈ A := by
    apply hKA
    apply hK.isClosed.closure_eq ▸ frontier_subset_closure
    rw [hboundary]
    exact mem_image_of_mem e
      (D.boundary_eq_neck_sphere.symm ▸ D.boundary_neck.center_on_central_sphere)
  have hAcomp : A ⊆ e '' connectedComponent D.boundary_neck.center := by
    rw [hecomponent]
    exact hA.subset_connectedComponent hcenter
  let V := e.symm '' interior K
  have hVopen : IsOpen V := e.symm.isOpenMap _ isOpen_interior
  have hVconn : IsConnected V := hKconn.image e.symm e.symm.continuous.continuousOn
  have hVcomp : V ⊆ connectedComponent D.boundary_neck.center := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨z, hz, rfl⟩ := hAcomp (hKA (interior_subset hy))
    simpa only [e.symm_apply_apply] using hz
  have hVavoid : Disjoint V D.boundary_sphere := by
    rw [disjoint_left]
    rintro _ ⟨y, hy, rfl⟩ hb
    have hyb : y ∈ frontier K := by
      rw [hboundary]
      exact ⟨e.symm y, hb, e.apply_symm_apply y⟩
    exact hyb.2 hy
  have hVext : V ⊆ connectedComponent D.boundary_neck.center \ D.closed_core := by
    rcases D.subset_core_or_compl_closed_core hVconn.isPreconnected hVavoid with hc | he
    · obtain ⟨p, hp⟩ := C.core_nonempty
      have hpK := hC (C.core_subset_closed_core hp)
      have hpV : e.symm p ∈ V := mem_image_of_mem e.symm hpK
      have hpD : p ∈ D.closed_core := hshrink
        ⟨e.symm p, D.core_subset_closed_core (hc hpV), e.apply_symm_apply p⟩
      exact (disjoint_left.mp hdis hpD (C.core_subset_carrier hp)).elim
    · exact fun _ hx => ⟨hVcomp hx, he hx⟩
  have hfrontV : frontier V ⊆ D.boundary_sphere := by
    rw [← e.symm.image_frontier]
    rintro _ ⟨y, hy, rfl⟩
    have hyb := frontier_interior_subset hy
    rw [hboundary] at hyb
    obtain ⟨z, hz, rfl⟩ := hyb
    simpa only [e.symm_apply_apply] using hz
  have hextV : connectedComponent D.boundary_neck.center \ D.closed_core ⊆ V := by
    apply connected_subset_open_of_disjoint_frontier
      D.isConnected_component_diff_closed_core hVopen
    · obtain ⟨p, hp⟩ := hVconn.nonempty
      exact ⟨p, hp, hVext hp⟩
    · exact disjoint_left.mpr (fun _ hx hf => hx.2 (D.boundary_subset_closed_core (hfrontV hf)))
  have hextK : e '' closure (connectedComponent D.boundary_neck.center \ D.closed_core) ⊆ K := by
    rw [e.image_closure]
    apply hK.isClosed.closure_subset_iff.mpr
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hzy⟩ := hextV hy
    have : e y = z := by rw [← hzy, e.apply_symm_apply]
    exact this.symm ▸ interior_subset hz
  obtain ⟨x, hxfront, hxD⟩ := hcontact
  have hxcomp : x ∈ e '' connectedComponent D.boundary_neck.center := by
    have hxcarrier : x ∈ e '' D.carrier := hcarrier.symm ▸ D.core_subset_carrier hxD
    exact image_mono D.carrier_subset_boundary_component hxcarrier
  have hpartition : e '' D.closed_core ∪
      e '' closure (connectedComponent D.boundary_neck.center \ D.closed_core) =
      e '' connectedComponent D.boundary_neck.center := by
    rw [← image_union, D.closed_core_union_closure_exterior]
  rw [← hpartition] at hxcomp
  rcases hxcomp with hxcore | hxext
  · exact ⟨x, hxfront, hxcore⟩
  · exact ((hAopen.frontier_eq ▸ hxfront).2 (hKA (hextK hxext))).elim

private theorem exists_aligned_compact_region (C : CapCertificate g) (N : EpsilonNeck g)
    {A K : Set M} (hNA : N.carrier ⊆ A) (havoid : Disjoint C.closed_core N.carrier)
    (hK : IsCompact K) (hKA : K ⊆ A) (hKconn : IsConnected (interior K))
    (hC : C.closed_core ⊆ interior K)
    {t : ℝ} (ht : t ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (hfront : frontier K = range (fun q : UnitTwoSphere => N.coordinate_map (q, t)))
    (h : UnitTwoSphere → ℝ) (hh : Continuous h)
    (hdom : ∀ q, h q ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    ∃ L : Set M, IsCompact L ∧ L ⊆ A ∧ IsConnected (interior L) ∧
      C.closed_core ⊆ interior L ∧
      frontier L = range (fun q => N.coordinate_map (q, h q)) := by
  obtain ⟨r, hr, hrN, hbound⟩ := N.exists_graph_collar h hh hdom
  obtain ⟨s, hs, hsN, htbound⟩ :=
    N.exists_graph_collar (fun _ => t) continuous_const (fun _ => ht)
  let e := N.graphTransport hr hrN h hh hbound
  let f := N.graphTransport hs hsN (fun _ => t) continuous_const htbound
  let k := f.symm.trans e
  have hfix {x : M} (hx : x ∉ N.carrier) : k x = x := by
    have he : e x = x := N.graphTransport_fixed hr hrN h hh hbound
      (fun h => hx (N.closedCollar_subset_carrier hrN h))
    have hf : f x = x := N.graphTransport_fixed hs hsN (fun _ => t) continuous_const htbound
      (fun h => hx (N.closedCollar_subset_carrier hsN h))
    have hfi : f.symm x = x := by apply f.injective; rw [f.apply_symm_apply, hf]
    change e (f.symm x) = x
    rw [hfi, he]
  have hA : k '' A = A := by
    have ho : EqOn k id Aᶜ := fun x hx => hfix (fun hy => hx (hNA hy))
    have hi := ho.image_eq_self
    rw [k.image_compl] at hi
    exact compl_injective hi
  have hfeq : f '' N.central_sphere =
      range (fun q : UnitTwoSphere => N.coordinate_map (q, t)) :=
    N.graphTransport_image_central_sphere hs hsN (fun _ => t) continuous_const htbound
  have heeq : e '' N.central_sphere = range (fun q => N.coordinate_map (q, h q)) :=
    N.graphTransport_image_central_sphere hr hrN h hh hbound
  refine ⟨k '' K, hK.image k.continuous, ?_, ?_, ?_, ?_⟩
  · exact (image_mono hKA).trans (subset_of_eq hA)
  · rw [← k.image_interior]
    exact hKconn.image k k.continuous.continuousOn
  · rw [← k.image_interior]
    exact fun x hx => ⟨x, hC hx, hfix (disjoint_left.mp havoid hx)⟩
  · rw [← k.image_frontier, hfront, ← hfeq]
    change (e ∘ f.symm) '' (f '' N.central_sphere) = _
    have hi : f.symm '' (f '' N.central_sphere) = N.central_sphere :=
      f.toEquiv.symm_image_image N.central_sphere
    rw [image_comp, hi, heeq]

private theorem coordinate_slice_in_core_or_end (D : CapCertificate g) {a : ℝ}
    (ha : a ∈ Ioo (-D.boundary_neck.epsilon⁻¹) D.boundary_neck.epsilon⁻¹)
    (hne : a ≠ 0) :
    (∀ q : UnitTwoSphere, D.boundary_neck.coordinate_map (q, a) ∈ D.core) ∨
      (∀ q : UnitTwoSphere, D.boundary_neck.coordinate_map (q, a) ∈ D.end_neck.carrier) := by
  have hmem {b c : ℝ} (hbc : a ∈ Ioo b c) (q : UnitTwoSphere) :
      D.boundary_neck.coordinate_map (q, a) ∈ D.boundary_neck.region b c := by
    refine ⟨D.boundary_neck.coordinate_map_mem ⟨mem_univ _, ha⟩, ?_⟩
    rwa [D.boundary_neck.coordinate_inverse_coordinate_map ⟨mem_univ _, ha⟩]
  rcases D.boundary_neck_sides with ⟨hn, hp⟩ | ⟨hp, hn⟩
  · rcases lt_or_gt_of_ne hne with hneg | hpos
    · exact Or.inl (fun q => hn (hmem ⟨ha.1, hneg⟩ q))
    · exact Or.inr (fun q => hp (hmem ⟨hpos, ha.2⟩ q))
  · rcases lt_or_gt_of_ne hne with hneg | hpos
    · exact Or.inr (fun q => hn (hmem ⟨ha.1, hneg⟩ q))
    · exact Or.inl (fun q => hp (hmem ⟨hpos, ha.2⟩ q))





theorem exists_outgoing_chain_boundary_transport_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 10000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ (C D : CapCertificate g), C.epsilon ≤ ε₀ → D.epsilon = C.epsilon →
        ∀ (H : ConnectedNeckCapCover g) (T : BalancedNeckChain g C.epsilon),
          C.IsOutgoingChain H T → ∀ b : ℤ, T.shape = .finite 0 b →
          Disjoint D.closed_core C.carrier →
          (frontier (C.carrier ∪ (T.unionOpen : Set M)) ∩ D.core).Nonempty →
          ∃ e : M ≃ₜ M,
            e '' D.boundary_sphere ⊆ C.carrier ∪ (T.unionOpen : Set M) ∧
            e '' D.carrier = D.carrier ∧
            (frontier (C.carrier ∪ (T.unionOpen : Set M)) ∩ (e '' D.closed_core)).Nonempty := by
  obtain ⟨ε₁, hε₁, hsmall, hshift⟩ :=
    exists_outgoing_chain_mixed_boundary_shifted_slice_threshold.{u}
  obtain ⟨ε₂, hε₂, -, hgraph⟩ := EpsilonNeck.exists_contained_coordinate_slice_graph.{u}
  obtain ⟨ε₃, hε₃, -, htrunc⟩ := exists_finite_chain_truncation_threshold.{u}
  obtain ⟨ε₄, hε₄, -, hintersection⟩ := exists_chain_intersection_threshold.{u}
  refine ⟨min ε₁ (min ε₂ (min ε₃ ε₄)),
    lt_min hε₁ (lt_min hε₂ (lt_min hε₃ hε₄)),
    (min_le_left _ _).trans hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g C D hε hDC H T hT b hshape hdis hcontact
  have h₁ := hε.trans (min_le_left _ _)
  have hrest := hε.trans (min_le_right _ _)
  have h₂ := hrest.trans (min_le_left _ _)
  have hrest := hrest.trans (min_le_right _ _)
  have h₃ := hrest.trans (min_le_left _ _)
  have h₄ := hrest.trans (min_le_right _ _)
  let A := C.carrier ∪ (T.unionOpen : Set M)
  have hAopen : IsOpen A := C.carrier_open.union T.unionOpen.isOpen
  by_cases hcontained : D.boundary_sphere ⊆ A
  · refine ⟨Homeomorph.refl M, ?_, ?_, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact hcontained hy
    · exact image_id D.carrier
    · obtain ⟨x, hx, hxD⟩ := hcontact
      exact ⟨x, hx, mem_image_of_mem _ (D.core_subset_closed_core hxD)⟩
  have hmeet := C.outgoing_chain_boundary_inter_nonempty D H T hT hdis hcontact
  obtain ⟨_, -, -, -, a, habs, ha, hhigh, -⟩ :=
    hshift C D h₁ hDC H T hT b hshape hmeet hcontained
  have hbnonneg : 0 ≤ b := by
    have hz := hT.zero_active
    simpa only [hshape, ChainShape.active, mem_Icc, le_refl, true_and] using hz
  have hb : b ∈ T.shape.active := by
    simpa only [hshape, ChainShape.active, mem_Icc] using And.intro hbnonneg (le_refl b)
  let N := T.neck b
  have hNε : N.epsilon = C.epsilon := T.epsilon_eq b hb
  have hNA : N.carrier ⊆ A := fun x hx => Or.inr (mem_iUnion.mpr ⟨⟨b, hb⟩, hx⟩)
  have hR : 0 < C.epsilon⁻¹ := inv_pos.mpr C.epsilon_pos
  have hane : a ≠ 0 := by
    intro hz
    rw [hz, abs_zero] at habs
    nlinarith
  obtain ⟨r, hr, hrD, habound⟩ := D.boundary_neck.exists_graph_collar
    (fun _ => a) continuous_const (fun _ => ha)
  let e := D.boundary_neck.graphTransport hr hrD (fun _ => a) continuous_const habound
  have heB : e '' D.boundary_sphere =
      range (fun q : UnitTwoSphere => D.boundary_neck.coordinate_map (q, a)) := by
    rw [D.boundary_eq_neck_sphere]
    exact D.boundary_neck.graphTransport_image_central_sphere hr hrD
      (fun _ => a) continuous_const habound
  have heBsub : e '' D.boundary_sphere ⊆ A := by
    rw [heB]
    exact hhigh.trans ((N.region_subset_carrier _ _).trans hNA)
  have heD : e '' D.carrier = D.carrier := by
    have hfix : EqOn e id D.carrierᶜ := by
      intro x hx
      exact D.boundary_neck.graphTransport_fixed hr hrD (fun _ => a) continuous_const habound
        (fun hy => hx (D.boundary_neck_subset
          (D.boundary_neck.closedCollar_subset_carrier hrD hy)))
    have hi := hfix.image_eq_self
    rw [e.image_compl] at hi
    exact compl_injective hi
  refine ⟨e, heBsub, heD, ?_⟩
  rcases coordinate_slice_in_core_or_end D ha hane with hcore | hend
  · have hshrink := D.graphTransport_closed_core_subset_of_graph_in_core
      hr hrD (fun _ => a) continuous_const habound hcore
    obtain ⟨h, hh, hdom, heq⟩ := hgraph N D.boundary_neck
      (hNε.trans_le h₂) ((D.boundary_neck_epsilon.trans hDC).trans_le h₂) ha
      (fun q => (hhigh (mem_range_self q)).1)
    let t := (0.75 : ℝ) * C.epsilon⁻¹
    have ht : t ∈ Ioo (C.epsilon⁻¹ / 2) C.epsilon⁻¹ := by
      dsimp only [t]
      constructor <;> linarith
    obtain ⟨hK, hKA, -, hfront, hC, hKconn⟩ := htrunc C h₃ H T hT b hshape t ht
    obtain ⟨-, havoid, -⟩ := hintersection C h₄ T 0 hT.zero_active hT.first_neck
      hT.nonnegative (fun j hj hjpos => (hT.centers j hj hjpos).2)
    have havoidN : Disjoint C.closed_core N.carrier :=
      havoid.mono_right (fun _ hx => mem_iUnion.mpr ⟨⟨b, hb⟩, hx⟩)
    have htN : t ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
      rw [hNε]
      exact ⟨by linarith [ht.1], ht.2⟩
    obtain ⟨L, hL, hLA, hLconn, hCL, hfrontL⟩ :=
      exists_aligned_compact_region C N hNA havoidN hK hKA hKconn hC htN hfront h hh hdom
    have hcenter : C.end_neck.center ∈ C.end_neck.carrier :=
      C.end_neck.central_sphere_subset C.end_neck.center_on_central_sphere
    have hA : IsConnected A := C.isConnected_carrier.union
      ⟨C.end_neck.center, C.end_neck_subset hcenter,
        mem_iUnion.mpr ⟨⟨0, hT.zero_active⟩, hT.first_neck.symm ▸ hcenter⟩⟩ T.isConnected_union
    apply contact_of_shrinking_transport_of_aligned_compact_region
      C D hA hAopen hL hLA hLconn hCL e _ heD hshrink hdis hcontact
    exact hfrontL.trans (heq.symm.trans heB.symm)
  · obtain ⟨x, hx, hxD⟩ := hcontact
    exact ⟨x, hx, D.closed_core_subset_graphTransport_of_graph_in_end
      hr hrD (fun _ => a) continuous_const habound hend (D.core_subset_closed_core hxD)⟩

end PoincareConjecture.CapCertificate
