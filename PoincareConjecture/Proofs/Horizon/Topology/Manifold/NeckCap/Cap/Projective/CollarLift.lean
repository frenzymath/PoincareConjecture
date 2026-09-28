import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Projective.CoreLift
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Collar
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Fibration.LiftedNeck

set_option autoImplicit false

noncomputable section

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] {g : RiemannianMetric 3 M}
  (C : CapCertificate g)
  (S : StandardPuncturedProjectiveCover M C.puncture C.carrier)

theorem exists_projective_boundary_collar_lift :
    ∃ F : C(NeckDomain C.boundary_neck.epsilon, UnitThreeSphere),
      IsOpenEmbedding F ∧
      (∀ z, Quotient.mk' (F z) ≠ C.puncture) ∧
      (∀ z, S.cover (F z) = C.boundary_neck.coordinate z) ∧
      Disjoint (range F) (range (fun z => -F z)) ∧
      {q : UnitThreeSphere | Quotient.mk' q ≠ C.puncture ∧
        S.cover q ∈ C.boundary_neck.carrier} =
          range F ∪ range (fun z => -F z) := by
  let N := C.boundary_neck
  let : SimplyConnectedSpace (NeckDomain N.epsilon) :=
    simplyConnectedSpace_neckDomain N.epsilon_pos
  let : LocallyPathConnectedSpace UnitTwoSphere :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 2)) UnitTwoSphere
  let : LocallyPathConnectedSpace (Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :=
    isOpen_Ioo.locallyPathConnectedSpace
  let f : NeckDomain N.epsilon → C.carrier :=
    fun z => ⟨N.coordinate z, C.boundary_neck_subset (N.coordinate z).property⟩
  have hf : IsOpenEmbedding f :=
    C.carrier_open.isOpenEmbedding_subtypeVal.of_comp f
      (N.carrier_open.isOpenEmbedding_subtypeVal.comp N.coordinate.isOpenEmbedding)
  let z₀ : NeckDomain N.epsilon :=
    (Poincare.Topology.standardSpherePole 0,
      ⟨0, neg_lt_zero.mpr (inv_pos.mpr N.epsilon_pos), inv_pos.mpr N.epsilon_pos⟩)
  obtain ⟨x₀, hx₀⟩ := S.restrictedCover_surjective (f z₀)
  obtain ⟨L, _, hL, hLo⟩ := Poincare.Topology.exists_openEmbedding_lift
    S.restrictedCover_isCoveringMap hf z₀ x₀ hx₀
  let F : C(NeckDomain N.epsilon, UnitThreeSphere) :=
    ⟨fun z => (L z).val, continuous_subtype_val.comp L.continuous⟩
  have hmem (z : NeckDomain N.epsilon) : Quotient.mk' (F z) ≠ C.puncture :=
    (L z).property
  have hlift (z : NeckDomain N.epsilon) : S.cover (F z) = N.coordinate z :=
    congrArg Subtype.val (congrFun hL z)
  have hnegmem (z : NeckDomain N.epsilon) : Quotient.mk' (-F z) ≠ C.puncture :=
    (PuncturedProjectiveSphere.antipode ⟨F z, hmem z⟩).property
  have hneglift (z : NeckDomain N.epsilon) : S.cover (-F z) = N.coordinate z :=
    ((S.fibers (-F z) (F z) (hnegmem z) (hmem z)).mpr (Or.inr rfl)).trans (hlift z)
  refine ⟨F, (isOpen_puncturedProjectiveSphere C.puncture).isOpenEmbedding_subtypeVal.comp hLo,
    hmem, hlift, ?_, ?_⟩
  · apply Set.disjoint_left.mpr
    rintro q ⟨a, ha⟩ ⟨b, hb⟩
    have heq : F a = -F b := ha.trans hb.symm
    have hab : a = b := N.coordinate.injective (Subtype.ext
      ((hlift a).symm.trans ((congrArg S.cover heq).trans (hneglift b))))
    subst b
    exact ne_neg_of_mem_unit_sphere ℝ (F a) heq
  · ext q
    constructor
    · rintro ⟨hq, hqN⟩
      let z := N.coordinate.symm ⟨S.cover q, hqN⟩
      have hz : (N.coordinate z : M) = S.cover q :=
        congrArg Subtype.val (N.coordinate.apply_symm_apply ⟨S.cover q, hqN⟩)
      have heq : S.cover q = S.cover (F z) := hz.symm.trans (hlift z).symm
      rcases (S.fibers q (F z) hq (hmem z)).mp heq with h | h
      · exact Or.inl ⟨z, h.symm⟩
      · exact Or.inr ⟨z, h.symm⟩
    · rintro (⟨z, rfl⟩ | ⟨z, rfl⟩)
      · exact ⟨hmem z, (hlift z).symm ▸ (N.coordinate z).property⟩
      · exact ⟨hnegmem z, (hneglift z).symm ▸ (N.coordinate z).property⟩

private theorem smooth_projective_boundary_collar_lift
    (e : OpenPartialHomeomorph RoundCylinderSpace UnitThreeSphere)
    (hes : e.source = C.boundary_neck.cylinderDomain)
    (hmem : ∀ z ∈ e.source, Quotient.mk' (e z) ≠ C.puncture)
    (hlift : ∀ z ∈ e.source, S.cover (e z) = C.boundary_neck.coordinate_map z) :
    ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ e e.source ∧
      ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ e.symm e.target := by
  let N := C.boundary_neck
  constructor
  · intro z hz
    obtain ⟨φ, hy, heq⟩ := S.local_diffeomorph ⟨e z, hmem z hz⟩
    have ht : N.coordinate_map z ∈ φ.target := by
      rw [← hlift z hz, heq hy]
      exact φ.map_source hy
    have hφ := φ.symm.contMDiffOn.contMDiffAt (φ.open_target.mem_nhds ht)
    have hN := N.coordinate_map_smooth.contMDiffAt (N.cylinderDomain_open.mem_nhds (hes ▸ hz))
    apply ((hφ.comp z hN).congr_of_eventuallyEq ?_).contMDiffWithinAt
    filter_upwards [e.open_source.mem_nhds hz,
      (e.continuousOn.continuousAt (e.open_source.mem_nhds hz))
        (φ.open_source.mem_nhds hy)] with w hw hwφ
    change e w = φ.symm (N.coordinate_map w)
    rw [← hlift w hw, heq hwφ]
    exact (φ.left_inv hwφ).symm
  · have heinv : EqOn (fun q => N.coordinate_inverse (S.cover q)) e.symm e.target := by
      intro q hq
      have h := N.coordinate_inverse_coordinate_map (hes ▸ e.map_target hq)
      rw [← hlift _ (e.map_target hq), e.right_inv hq] at h
      exact h
    apply ContMDiffOn.congr _ heinv.symm
    intro q hq
    have hqmem : Quotient.mk' q ≠ C.puncture := by
      simpa only [e.right_inv hq] using hmem _ (e.map_target hq)
    have hqN : S.cover q ∈ N.carrier := by
      rw [← e.right_inv hq, hlift _ (e.map_target hq)]
      exact N.coordinate_map_mem (hes ▸ e.map_target hq)
    exact ((N.coordinate_inverse_smooth.contMDiffAt (N.carrier_open.mem_nhds hqN)).comp q
      (S.local_diffeomorph ⟨q, hqmem⟩).contMDiffAt).contMDiffWithinAt

theorem exists_smooth_projective_boundary_collar :
    ∃ e : OpenPartialHomeomorph RoundCylinderSpace UnitThreeSphere,
      e.source = C.boundary_neck.cylinderDomain ∧
      ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ e e.source ∧
      ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ e.symm e.target ∧
      (∀ z ∈ e.source, Quotient.mk' (e z) ≠ C.puncture) ∧
      (∀ z ∈ e.source, S.cover (e z) = C.boundary_neck.coordinate_map z) ∧
      Disjoint e.target (Neg.neg '' e.target) ∧
      {q : UnitThreeSphere | Quotient.mk' q ≠ C.puncture ∧
        S.cover q ∈ C.boundary_neck.carrier} = e.target ∪ Neg.neg '' e.target := by
  obtain ⟨F, hF, hmem, hlift, hdisj, hexhaust⟩ := C.exists_projective_boundary_collar_lift S
  let N := C.boundary_neck
  let : Nonempty (NeckDomain N.epsilon) := ⟨Poincare.Topology.standardSpherePole 0,
    ⟨0, neg_lt_zero.mpr (inv_pos.mpr N.epsilon_pos), inv_pos.mpr N.epsilon_pos⟩⟩
  let v : NeckDomain N.epsilon → RoundCylinderSpace := fun z => (z.1, z.2.val)
  have hv : IsOpenEmbedding v := IsOpenEmbedding.id.prodMap isOpen_Ioo.isOpenEmbedding_subtypeVal
  let a := hv.toOpenPartialHomeomorph v
  let b := hF.toOpenPartialHomeomorph F
  let e := a.symm.trans b
  have hvrange : range v = N.cylinderDomain := by
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨mem_univ _, w.2.property⟩
    · intro hz
      exact ⟨(z.1, ⟨z.2, hz.2⟩), rfl⟩
  have hes : e.source = N.cylinderDomain := by
    simpa only [e, a, b, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.symm_source, IsOpenEmbedding.toOpenPartialHomeomorph_source,
      IsOpenEmbedding.toOpenPartialHomeomorph_target, preimage_univ, inter_univ,
      image_univ] using hvrange
  have het : e.target = range F := by
    simp [e, a, b]
  have heapply (z : NeckDomain N.epsilon) : e (v z) = F z := by
    change F (a.symm (v z)) = F z
    rw [hv.toOpenPartialHomeomorph_left_inv]
  have hemem (z : RoundCylinderSpace) (hz : z ∈ e.source) :
      Quotient.mk' (e z) ≠ C.puncture := by
    obtain ⟨w, rfl⟩ := hvrange.symm ▸ (hes ▸ hz)
    rw [heapply]
    exact hmem w
  have helift (z : RoundCylinderSpace) (hz : z ∈ e.source) :
      S.cover (e z) = N.coordinate_map z := by
    obtain ⟨w, rfl⟩ := hvrange.symm ▸ (hes ▸ hz)
    rw [heapply, hlift]
    exact N.coordinate_map_eq w
  have hneg : Neg.neg '' e.target = range (fun z => -F z) := by
    rw [het, ← range_comp]
    rfl
  obtain ⟨he, hei⟩ := C.smooth_projective_boundary_collar_lift S e hes hemem helift
  refine ⟨e, hes, he, hei, hemem, helift, ?_, ?_⟩
  · rw [hneg, het]
    exact hdisj
  · rw [hneg, het]
    exact hexhaust

theorem projective_boundary_collar_frontier
    (e : OpenPartialHomeomorph RoundCylinderSpace UnitThreeSphere)
    (hes : e.source = C.boundary_neck.cylinderDomain)
    (hmem : ∀ z ∈ e.source, Quotient.mk' (e z) ≠ C.puncture)
    (hlift : ∀ z ∈ e.source, S.cover (e z) = C.boundary_neck.coordinate_map z) :
    frontier (C.projectiveClosedCoreLift S) ∩ e.target =
      e '' (univ ×ˢ ({0} : Set ℝ)) := by
  have : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ ‹T3Space M›)
  let N := C.boundary_neck
  have hzero (p : UnitTwoSphere) : (p, (0 : ℝ)) ∈ e.source := by
    rw [hes]
    exact ⟨mem_univ _, neg_lt_zero.mpr (inv_pos.mpr N.epsilon_pos), inv_pos.mpr N.epsilon_pos⟩
  rw [C.frontier_projectiveClosedCoreLift S, C.boundary_eq_neck_sphere]
  ext q
  constructor
  · rintro ⟨⟨_, hq⟩, hqt⟩
    let z := e.symm q
    have hzs : z ∈ e.source := e.map_target hqt
    have hcoord : N.coordinate_map z = S.cover q := by
      rw [← hlift z hzs, e.right_inv hqt]
    have hz0 : z.2 = 0 := by
      have hz := (N.mem_central_sphere_iff _).mp hq
      rw [← hcoord, N.coordinate_inverse_coordinate_map (hes ▸ hzs)] at hz
      exact hz.2
    exact ⟨z, ⟨mem_univ _, hz0⟩, e.right_inv hqt⟩
  · rintro ⟨⟨p, t⟩, ⟨_, ht⟩, rfl⟩
    have ht0 : t = 0 := ht
    subst t
    refine ⟨⟨hmem _ (hzero p), ?_⟩, e.map_source (hzero p)⟩
    rw [hlift _ (hzero p), ← N.centralSphere_range]
    exact mem_range_self p

theorem projective_boundary_collar_sides [T2Space M]
    (e : OpenPartialHomeomorph RoundCylinderSpace UnitThreeSphere)
    (hes : e.source = C.boundary_neck.cylinderDomain)
    (hmem : ∀ z ∈ e.source, Quotient.mk' (e z) ≠ C.puncture)
    (hlift : ∀ z ∈ e.source, S.cover (e z) = C.boundary_neck.coordinate_map z) :
    (e '' (univ ×ˢ Ioo (-C.boundary_neck.epsilon⁻¹) 0) ⊆
        interior (C.projectiveClosedCoreLift S) ∧
      e '' (univ ×ˢ Ioo 0 C.boundary_neck.epsilon⁻¹) ⊆
        (C.projectiveClosedCoreLift S)ᶜ) ∨
    (e '' (univ ×ˢ Ioo 0 C.boundary_neck.epsilon⁻¹) ⊆
        interior (C.projectiveClosedCoreLift S) ∧
      e '' (univ ×ˢ Ioo (-C.boundary_neck.epsilon⁻¹) 0) ⊆
        (C.projectiveClosedCoreLift S)ᶜ) := by
  let N := C.boundary_neck
  have hin {z : RoundCylinderSpace} (hz : z ∈ e.source)
      (hcore : N.coordinate_map z ∈ C.core) :
      e z ∈ interior (C.projectiveClosedCoreLift S) := by
    rw [C.interior_projectiveClosedCoreLift S]
    exact ⟨hmem z hz, (hlift z hz).symm ▸ hcore⟩
  have hout {z : RoundCylinderSpace} (hz : z ∈ e.source)
      (hend : N.coordinate_map z ∈ C.end_neck.carrier) :
      e z ∈ (C.projectiveClosedCoreLift S)ᶜ := by
    intro hq
    have hcore : S.cover (e z) ∈ C.closed_core := hq.2
    rw [hlift z hz] at hcore
    exact Set.disjoint_left.mp C.disjoint_closed_core_end hcore hend
  have hregion {z : RoundCylinderSpace} {a b : ℝ}
      (hz : z ∈ N.cylinderDomain) (hzab : z.2 ∈ Ioo a b) :
      N.coordinate_map z ∈ N.region a b := by
    refine ⟨N.coordinate_map_mem hz, ?_⟩
    rw [N.coordinate_inverse_coordinate_map hz]
    exact hzab
  have hneg {z : RoundCylinderSpace} (hz : z ∈ univ ×ˢ Ioo (-N.epsilon⁻¹) 0) :
      z ∈ e.source ∧ N.coordinate_map z ∈ N.region (-N.epsilon⁻¹) 0 := by
    have hzN : z ∈ N.cylinderDomain :=
      ⟨hz.1, hz.2.1, hz.2.2.trans (inv_pos.mpr N.epsilon_pos)⟩
    exact ⟨hes.symm ▸ hzN, hregion hzN hz.2⟩
  have hpos {z : RoundCylinderSpace} (hz : z ∈ univ ×ˢ Ioo 0 N.epsilon⁻¹) :
      z ∈ e.source ∧ N.coordinate_map z ∈ N.region 0 N.epsilon⁻¹ := by
    have hzN : z ∈ N.cylinderDomain :=
      ⟨hz.1, (neg_lt_zero.mpr (inv_pos.mpr N.epsilon_pos)).trans hz.2.1, hz.2.2⟩
    exact ⟨hes.symm ▸ hzN, hregion hzN hz.2⟩
  rcases C.boundary_neck_sides with ⟨hn, hp⟩ | ⟨hp, hn⟩
  · left
    constructor
    · rintro _ ⟨z, hz, rfl⟩
      exact hin (hneg hz).1 (hn (hneg hz).2)
    · rintro _ ⟨z, hz, rfl⟩
      exact hout (hpos hz).1 (hp (hpos hz).2)
  · right
    constructor
    · rintro _ ⟨z, hz, rfl⟩
      exact hin (hpos hz).1 (hp (hpos hz).2)
    · rintro _ ⟨z, hz, rfl⟩
      exact hout (hneg hz).1 (hn (hneg hz).2)

end PoincareConjecture.CapCertificate
