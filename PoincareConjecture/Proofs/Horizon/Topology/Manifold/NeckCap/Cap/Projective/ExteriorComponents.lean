import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Projective.CollarLift
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.CountableComplement













noncomputable section
set_option autoImplicit false

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



theorem exists_projective_end_neck_lift :
    ∃ F : C(NeckDomain C.end_neck.epsilon, UnitThreeSphere),
      IsOpenEmbedding F ∧
      IsConnected (range F) ∧
      (∀ z, Quotient.mk' (F z) ≠ C.puncture) ∧
      (∀ z, S.cover (F z) = C.end_neck.coordinate z) ∧
      Disjoint (range F) (range (fun z => -F z)) ∧
      {q : UnitThreeSphere | Quotient.mk' q ≠ C.puncture ∧
        S.cover q ∈ C.end_neck.carrier} =
          range F ∪ range (fun z => -F z) := by
  let N := C.end_neck
  let : SimplyConnectedSpace (NeckDomain N.epsilon) :=
    simplyConnectedSpace_neckDomain N.epsilon_pos
  let : LocallyPathConnectedSpace UnitTwoSphere :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 2)) UnitTwoSphere
  let : LocallyPathConnectedSpace (Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :=
    isOpen_Ioo.locallyPathConnectedSpace
  let f : NeckDomain N.epsilon → C.carrier :=
    fun z => ⟨N.coordinate z, C.end_neck_subset (N.coordinate z).property⟩
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
    isConnected_range F.continuous, hmem, hlift, ?_, ?_⟩
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


theorem neg_mem_projectiveClosedCoreLift_iff (q : UnitThreeSphere) :
    -q ∈ C.projectiveClosedCoreLift S ↔ q ∈ C.projectiveClosedCoreLift S := by
  have hp : (Quotient.mk' (-q) : RealProjectiveThree) = Quotient.mk' q :=
    Quotient.sound (Or.inr rfl)
  change (Quotient.mk' (-q) ≠ C.puncture ∧ S.cover (-q) ∈ C.closed_core) ↔
    (Quotient.mk' q ≠ C.puncture ∧ S.cover q ∈ C.closed_core)
  constructor
  · rintro ⟨hq, hc⟩
    have hq' : Quotient.mk' q ≠ C.puncture := hp ▸ hq
    have heq := (S.fibers (-q) q hq hq').mpr (Or.inr rfl)
    exact ⟨hq', heq ▸ hc⟩
  · rintro ⟨hq, hc⟩
    have hq' : Quotient.mk' (-q) ≠ C.puncture := hp.symm ▸ hq
    have heq := (S.fibers (-q) q hq' hq).mpr (Or.inr rfl)
    exact ⟨hq', heq.symm ▸ hc⟩



theorem compl_projectiveClosedCoreLift :
    (C.projectiveClosedCoreLift S)ᶜ =
      {q : UnitThreeSphere | Quotient.mk' q = C.puncture} ∪
      {q : UnitThreeSphere | Quotient.mk' q ≠ C.puncture ∧
        S.cover q ∈ C.end_neck.carrier} := by
  ext q
  constructor
  · intro hq
    by_cases hp : Quotient.mk' q = C.puncture
    · exact Or.inl hp
    · right
      refine ⟨hp, ?_⟩
      have hcar : S.cover q ∈ C.carrier :=
        S.image_eq.subset (mem_image_of_mem S.cover hp)
      rcases C.carrier_eq_closed_core_union_end.subset hcar with hc | he
      · exact (hq ⟨hp, hc⟩).elim
      · exact he
  · rintro (hp | ⟨hp, he⟩) ⟨hq, hc⟩
    · exact hq hp
    · exact Set.disjoint_left.mp C.disjoint_closed_core_end hc he

end PoincareConjecture.CapCertificate

namespace PoincareConjecture

private theorem exterior_of_collar_partition
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X Y) {L Z R : Set X} {D : Set Y}
    (hs : e.source ⊆ L ∪ Z ∪ R) (hR : R ⊆ e.source)
    (hL : e '' L ⊆ D) (hZ : e '' Z ⊆ D) (hout : e '' R ⊆ Dᶜ) :
    Dᶜ ∩ e.target = e '' R := by
  apply Subset.antisymm
  · intro y hy
    have hz := hs (e.map_target hy.2)
    rcases hz with (hz | hz) | hz
    · exact (hy.1 (hL ⟨e.symm y, hz, e.right_inv hy.2⟩)).elim
    · exact (hy.1 (hZ ⟨e.symm y, hz, e.right_inv hy.2⟩)).elim
    · exact ⟨e.symm y, hz, e.right_inv hy.2⟩
  · rintro y ⟨x, hx, rfl⟩
    exact ⟨hout (mem_image_of_mem e hx), e.map_source (hR hx)⟩

private theorem disjoint_closures_of_local_exterior
    {X : Type*} [TopologicalSpace X] {K A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B)
    (hdis : Disjoint A B) (hcover : A ∪ B = Kᶜ)
    (hlocal : ∀ x ∈ frontier K, ∃ V : Set X,
      IsOpen V ∧ x ∈ V ∧ IsPreconnected (Kᶜ ∩ V)) :
    Disjoint (closure A) (closure B) := by
  apply disjoint_left.mpr
  intro x hxA hxB
  have hAK : A ⊆ Kᶜ := subset_union_left.trans hcover.subset
  have hxK : x ∈ K := by
    by_contra hxK
    rcases hcover.symm.subset hxK with hx | hx
    · obtain ⟨y, hyA, hyB⟩ := mem_closure_iff.mp hxB A hA hx
      exact disjoint_left.mp hdis hyA hyB
    · obtain ⟨y, hyB, hyA⟩ := mem_closure_iff.mp hxA B hB hx
      exact disjoint_left.mp hdis hyA hyB
  have hxfront : x ∈ frontier K := by
    rw [frontier_eq_closure_inter_closure]
    exact ⟨subset_closure hxK, closure_mono hAK hxA⟩
  obtain ⟨V, hV, hxV, hcV⟩ := hlocal x hxfront
  obtain ⟨y, hyV, hyA⟩ := mem_closure_iff.mp hxA V hV hxV
  obtain ⟨z, hzV, hzB⟩ := mem_closure_iff.mp hxB V hV hxV
  rcases hcV.subset_or_subset hA hB hdis
    (fun q hq => hcover.symm.subset hq.1) with hs | hs
  · exact disjoint_left.mp hdis (hs ⟨hcover.subset (Or.inr hzB), hzV⟩) hzB
  · exact disjoint_left.mp hdis hyA (hs ⟨hcover.subset (Or.inl hyA), hyV⟩)

private theorem frontier_of_disjoint_exterior_closures
    {X : Type*} [TopologicalSpace X] {K A B G H : Set X}
    (hK : IsClosed K) (hA : IsOpen A)
    (hdis : Disjoint (closure A) (closure B)) (hcover : A ∪ B = Kᶜ)
    (hfront : frontier K = G ∪ H) (hG : G ⊆ closure A) (hH : H ⊆ closure B) :
    frontier A = G := by
  have hAK : A ⊆ Kᶜ := subset_union_left.trans hcover.subset
  rw [hA.frontier_eq]
  apply Subset.antisymm
  · intro x hx
    have hxK : x ∈ K := by
      by_contra hn
      have hxB := (hcover.symm.subset hn).resolve_left hx.2
      exact disjoint_left.mp hdis hx.1 (subset_closure hxB)
    have hxfront : x ∈ frontier K := by
      rw [frontier_eq_closure_inter_closure]
      exact ⟨subset_closure hxK, closure_mono hAK hx.1⟩
    rcases hfront.subset hxfront with hxG | hxH
    · exact hxG
    · exact (disjoint_left.mp hdis hx.1 (hH hxH)).elim
  · intro x hx
    refine ⟨hG hx, ?_⟩
    intro hxA
    exact hAK hxA (hK.frontier_subset (hfront.symm.subset (Or.inl hx)))

private theorem antipodal_exterior_components
    {K V : Set UnitThreeSphere} (hK : IsClosed K)
    (hnegK : ∀ x, -x ∈ K ↔ x ∈ K)
    (a : UnitThreeSphere) (ha : a ∉ K)
    (hV : IsOpen V) (hcV : IsConnected V)
    (hdisV : Disjoint V (Neg.neg '' V))
    (hcover : Kᶜ \ {a, -a} = V ∪ Neg.neg '' V) :
    let A := connectedComponentIn Kᶜ a
    IsOpen A ∧ IsConnected A ∧
      Disjoint A (Neg.neg '' A) ∧ A ∪ Neg.neg '' A = Kᶜ ∧
      a ∈ A ∧ -a ∉ A := by
  let : LocallyPathConnectedSpace UnitThreeSphere :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 3)) UnitThreeSphere
  let A := connectedComponentIn Kᶜ a
  have hA : IsOpen A := hK.isOpen_compl.connectedComponentIn
  have hcA : IsConnected A := isConnected_connectedComponentIn_iff.mpr ha
  have haA : a ∈ A := mem_connectedComponentIn ha
  have hAsub : A ⊆ Kᶜ := connectedComponentIn_subset _ _
  have hnegA : IsOpen (Neg.neg '' A) := (Homeomorph.neg UnitThreeSphere).isOpenMap _ hA
  have hcnegA : IsConnected (Neg.neg '' A) := hcA.image _ continuous_neg.continuousOn
  have hnegAsub : Neg.neg '' A ⊆ Kᶜ := by
    rintro _ ⟨x, hx, rfl⟩ hn
    exact hAsub hx ((hnegK x).mp hn)
  have hnegV : IsOpen (Neg.neg '' V) := (Homeomorph.neg UnitThreeSphere).isOpenMap _ hV
  have hcV' : IsConnected (A \ {a, -a}) :=
    Poincare.Topology.Manifold.isConnected_sdiff_countable_of_isOpen (n := 1)
      hA hcA ((finite_singleton (-a)).insert a).countable
  have hside : A \ {a, -a} ⊆ V ∨ A \ {a, -a} ⊆ Neg.neg '' V :=
    hcV'.isPreconnected.subset_or_subset hV hnegV hdisV
      (by rw [← hcover]; exact sdiff_subset_sdiff_left hAsub)
  have hnegAsame : Neg.neg '' A = connectedComponentIn Kᶜ (-a) := by
    have hKneg : (Homeomorph.neg UnitThreeSphere) '' Kᶜ = Kᶜ := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩ h
        exact hy ((hnegK y).mp h)
      · intro hx
        exact ⟨-x, fun h => hx ((hnegK x).mp h), neg_neg x⟩
    have h := (Homeomorph.neg UnitThreeSphere).image_connectedComponentIn
      (s := Kᶜ) (x := a) ha
    rw [hKneg] at h
    exact h
  have hneq : A ≠ Neg.neg '' A := by
    intro heq
    obtain ⟨x, hxA, hxp⟩ := hcV'.nonempty
    have hnA : -x ∈ A := heq.symm ▸ mem_image_of_mem Neg.neg hxA
    have hnp : -x ∉ ({a, -a} : Set UnitThreeSphere) := by
      intro h
      have he : -x = a ∨ -x = -a := by simpa using h
      apply hxp
      simp only [mem_insert_iff, mem_singleton_iff]
      rcases he with he | he
      · exact Or.inr (neg_eq_iff_eq_neg.mp he)
      · exact Or.inl (neg_inj.mp he)
    rcases hside with hs | hs
    · exact Set.disjoint_left.mp hdisV (hs ⟨hnA, hnp⟩)
        (mem_image_of_mem Neg.neg (hs ⟨hxA, hxp⟩))
    · obtain ⟨y, hy, hyx⟩ := hs ⟨hxA, hxp⟩
      have hnV : -x ∈ V := by simpa only [← hyx, neg_neg] using hy
      exact Set.disjoint_left.mp hdisV hnV (hs ⟨hnA, hnp⟩)
  have hdisA : Disjoint A (Neg.neg '' A) := by
    apply disjoint_left.mpr
    intro x hx hn
    apply hneq
    rw [hnegAsame] at hn ⊢
    exact (connectedComponentIn_eq hx).trans (connectedComponentIn_eq hn).symm
  have hminus : -a ∉ A := by
    intro h
    exact Set.disjoint_left.mp hdisA h (mem_image_of_mem Neg.neg haA)
  have hVsub : V ⊆ Kᶜ := by
    intro x hx
    exact (hcover.symm.subset (Or.inl hx)).1
  have hV'sub : Neg.neg '' V ⊆ Kᶜ := by
    intro x hx
    exact (hcover.symm.subset (Or.inr hx)).1
  have hsame {W : Set UnitThreeSphere} (hcW : IsConnected W) (hW : W ⊆ Kᶜ)
      (hAW : A \ {a, -a} ⊆ W) : W ⊆ A := by
    obtain ⟨x, hxA, hxp⟩ := hcV'.nonempty
    rw [show A = connectedComponentIn Kᶜ x from connectedComponentIn_eq hxA]
    exact hcW.isPreconnected.subset_connectedComponentIn (hAW ⟨hxA, hxp⟩) hW
  have hcoverA : A ∪ Neg.neg '' A = Kᶜ := by
    apply Subset.antisymm (union_subset hAsub hnegAsub)
    intro x hx
    by_cases hxp : x ∈ ({a, -a} : Set UnitThreeSphere)
    · rcases (show x = a ∨ x = -a by simpa using hxp) with h | h
      · exact Or.inl (h.symm ▸ haA)
      · exact Or.inr (h.symm ▸ mem_image_of_mem Neg.neg haA)
    · have hxV : x ∈ V ∪ Neg.neg '' V := hcover ▸ ⟨hx, hxp⟩
      rcases hside with hs | hs
      · have hVA := hsame hcV hVsub hs
        rcases hxV with hxV | ⟨y, hy, rfl⟩
        · exact Or.inl (hVA hxV)
        · exact Or.inr (mem_image_of_mem Neg.neg (hVA hy))
      · have hVA := hsame (hcV.image _ continuous_neg.continuousOn) hV'sub hs
        rcases hxV with hxV | hxV
        · right
          exact ⟨-x, hVA (mem_image_of_mem Neg.neg hxV), neg_neg x⟩
        · exact Or.inl (hVA hxV)
  exact ⟨hA, hcA, hdisA, hcoverA, haA, hminus⟩

namespace CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] {g : RiemannianMetric 3 M}
  (C : CapCertificate g)
  (S : StandardPuncturedProjectiveCover M C.puncture C.carrier)



theorem isConnected_projective_boundary_collar_exterior [T2Space M]
    (e : OpenPartialHomeomorph RoundCylinderSpace UnitThreeSphere)
    (hes : e.source = C.boundary_neck.cylinderDomain)
    (hmem : ∀ z ∈ e.source, Quotient.mk' (e z) ≠ C.puncture)
    (hlift : ∀ z ∈ e.source, S.cover (e z) = C.boundary_neck.coordinate_map z) :
    IsConnected ((C.projectiveClosedCoreLift S)ᶜ ∩ e.target) := by
  let δ := C.boundary_neck.epsilon⁻¹
  have hδ : 0 < δ := inv_pos.mpr C.boundary_neck.epsilon_pos
  let L : Set RoundCylinderSpace := univ ×ˢ Ioo (-δ) 0
  let Z : Set RoundCylinderSpace := univ ×ˢ ({0} : Set ℝ)
  let R : Set RoundCylinderSpace := univ ×ˢ Ioo 0 δ
  have hL : L ⊆ e.source := by
    intro z hz
    rw [hes]
    exact ⟨hz.1, hz.2.1, hz.2.2.trans hδ⟩
  have hR : R ⊆ e.source := by
    intro z hz
    rw [hes]
    exact ⟨hz.1, (neg_lt_zero.mpr hδ).trans hz.2.1, hz.2.2⟩
  have hcover : e.source ⊆ L ∪ Z ∪ R := by
    intro z hz
    rw [hes] at hz
    rcases lt_trichotomy z.2 0 with ht | ht | ht
    · exact Or.inl (Or.inl ⟨mem_univ _, hz.2.1, ht⟩)
    · exact Or.inl (Or.inr ⟨mem_univ _, ht⟩)
    · exact Or.inr ⟨mem_univ _, ht, hz.2.2⟩
  have hZ : e '' Z ⊆ C.projectiveClosedCoreLift S := by
    intro q hq
    have hf := (C.projective_boundary_collar_frontier S e hes hmem hlift).symm.subset hq
    exact (C.isCompact_projectiveClosedCoreLift S).isClosed.frontier_subset hf.1
  have hcL : IsConnected (e '' L) :=
    (isConnected_univ.prod (isConnected_Ioo (neg_lt_zero.mpr hδ))).image e
      (e.continuousOn.mono hL)
  have hcR : IsConnected (e '' R) :=
    (isConnected_univ.prod (isConnected_Ioo hδ)).image e (e.continuousOn.mono hR)
  rcases C.projective_boundary_collar_sides S e hes hmem hlift with ⟨hi, ho⟩ | ⟨hi, ho⟩
  · rw [exterior_of_collar_partition e hcover hR (hi.trans interior_subset) hZ ho]
    exact hcR
  · have hcover' : e.source ⊆ R ∪ Z ∪ L := by
      intro z hz
      rcases hcover hz with (hz | hz) | hz
      · exact Or.inr hz
      · exact Or.inl (Or.inr hz)
      · exact Or.inl (Or.inl hz)
    rw [exterior_of_collar_partition e hcover' hL (hi.trans interior_subset) hZ ho]
    exact hcL




theorem projectiveClosedCoreLift_exterior_components
    (a : UnitThreeSphere) (ha : Quotient.mk' a = C.puncture) :
    let A := connectedComponentIn (C.projectiveClosedCoreLift S)ᶜ a
    IsOpen A ∧ IsConnected A ∧
      Disjoint A (Neg.neg '' A) ∧
      A ∪ Neg.neg '' A = (C.projectiveClosedCoreLift S)ᶜ ∧
      a ∈ A ∧ -a ∉ A := by
  obtain ⟨F, hF, hcF, hmem, _, hdis, hexhaust⟩ := C.exists_projective_end_neck_lift S
  have hneg : Neg.neg '' range F = range (fun z => -F z) := by
    rw [← range_comp]
    rfl
  have hp : {q : UnitThreeSphere | Quotient.mk' q = C.puncture} = {a, -a} := by
    ext q
    rw [← ha]
    exact Quotient.eq
  apply antipodal_exterior_components (C.isCompact_projectiveClosedCoreLift S).isClosed
    (C.neg_mem_projectiveClosedCoreLift_iff S) a (fun h => h.1 ha)
    hF.isOpen_range hcF
  · rwa [hneg]
  · rw [C.compl_projectiveClosedCoreLift S, hp, union_sdiff_left, hexhaust, ← hneg]
    apply sdiff_eq_left.mpr
    apply disjoint_left.mpr
    intro q hq hqp
    have hqm : Quotient.mk' q ≠ C.puncture := by
      rw [hneg] at hq
      exact (hexhaust.symm ▸ hq).1
    exact hqm (hp.symm.subset hqp)



theorem disjoint_closure_projectiveClosedCoreLift_exterior [T2Space M]
    (a : UnitThreeSphere) (ha : Quotient.mk' a = C.puncture) :
    let A := connectedComponentIn (C.projectiveClosedCoreLift S)ᶜ a
    Disjoint (closure A) (closure (Neg.neg '' A)) := by
  obtain ⟨hA, hcA, hdis, hcover, _⟩ := C.projectiveClosedCoreLift_exterior_components S a ha
  apply disjoint_closures_of_local_exterior hA
    ((Homeomorph.neg UnitThreeSphere).isOpenMap _ hA) hdis hcover
  obtain ⟨e, hes, _, _, hmem, hlift, _, hexhaust⟩ :=
    C.exists_smooth_projective_boundary_collar S
  have hc := C.isConnected_projective_boundary_collar_exterior S e hes hmem hlift
  have hneg : Neg.neg '' ((C.projectiveClosedCoreLift S)ᶜ ∩ e.target) =
      (C.projectiveClosedCoreLift S)ᶜ ∩ Neg.neg '' e.target := by
    ext q
    constructor
    · rintro ⟨y, ⟨hyK, hyt⟩, rfl⟩
      exact ⟨fun h => hyK ((C.neg_mem_projectiveClosedCoreLift_iff S y).mp h),
        mem_image_of_mem Neg.neg hyt⟩
    · rintro ⟨hqK, y, hyt, rfl⟩
      exact ⟨y, ⟨fun h => hqK ((C.neg_mem_projectiveClosedCoreLift_iff S y).mpr h), hyt⟩, rfl⟩
  have hcneg : IsConnected ((C.projectiveClosedCoreLift S)ᶜ ∩ Neg.neg '' e.target) := by
    rw [← hneg]
    exact hc.image _ continuous_neg.continuousOn
  intro q hq
  have hfront := (C.frontier_projectiveClosedCoreLift S).subset hq
  have hbn : C.boundary_sphere ⊆ C.boundary_neck.carrier := by
    rw [C.boundary_eq_neck_sphere]
    exact C.boundary_neck.central_sphere_subset
  rcases hexhaust.subset ⟨hfront.1, hbn hfront.2⟩ with ht | ht
  · exact ⟨e.target, e.open_target, ht, hc.isPreconnected⟩
  · exact ⟨Neg.neg '' e.target, (Homeomorph.neg UnitThreeSphere).isOpenMap _ e.open_target,
      ht, hcneg.isPreconnected⟩



theorem exists_projective_exterior_frontier_sphere [T2Space M]
    (a : UnitThreeSphere) (ha : Quotient.mk' a = C.puncture) :
    let A := connectedComponentIn (C.projectiveClosedCoreLift S)ᶜ a
    ∃ F : UnitTwoSphere → UnitThreeSphere,
      Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ F ∧
      Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (fun q => -F q) ∧
      (∀ q, Quotient.mk' (F q) ≠ C.puncture) ∧
      (∀ q, S.cover (F q) = C.boundary_neck.coordinate_map (q, 0)) ∧
      frontier A = range F ∧ frontier (Neg.neg '' A) = range (fun q => -F q) := by
  let K := C.projectiveClosedCoreLift S
  let A := connectedComponentIn Kᶜ a
  let B := Neg.neg '' A
  have hK : IsClosed K := (C.isCompact_projectiveClosedCoreLift S).isClosed
  obtain ⟨hA, hcA, _, hcover, _⟩ := C.projectiveClosedCoreLift_exterior_components S a ha
  have hB : IsOpen B := (Homeomorph.neg UnitThreeSphere).isOpenMap _ hA
  have hdis : Disjoint (closure A) (closure B) :=
    C.disjoint_closure_projectiveClosedCoreLift_exterior S a ha
  obtain ⟨F, hF, hnegF, hmem, hlift, _, hfront⟩ :=
    C.exists_projectiveClosedCoreLift_frontier_spheres S
  have hclcover : frontier K ⊆ closure A ∪ closure B := by
    rw [← closure_union, hcover]
    intro q hq
    rw [frontier_eq_closure_inter_closure] at hq
    exact hq.2
  have hFcover : range F ⊆ closure A ∪ closure B :=
    subset_union_left.trans (hfront.symm.subset.trans hclcover)
  have hcF : IsPreconnected (range F) := (isConnected_range hF.contMDiff.continuous).isPreconnected
  have hside : range F ⊆ closure A ∨ range F ⊆ closure B := by
    by_cases hmeet : (range F ∩ closure A).Nonempty
    · left
      intro q hq
      by_contra hn
      have hqB := (hFcover hq).resolve_left hn
      obtain ⟨x, _, hxA, hxB⟩ := isPreconnected_closed_iff.mp hcF
        (closure A) (closure B) isClosed_closure isClosed_closure hFcover hmeet ⟨q, hq, hqB⟩
      exact disjoint_left.mp hdis hxA hxB
    · right
      intro q hq
      exact (hFcover hq).resolve_left (fun h => hmeet ⟨q, hq, h⟩)
  have hnegA (q : UnitThreeSphere) (hq : q ∈ closure A) : -q ∈ closure B := by
    have h := mem_image_of_mem (Homeomorph.neg UnitThreeSphere) hq
    rw [(Homeomorph.neg UnitThreeSphere).image_closure] at h
    exact h
  have hnegB (q : UnitThreeSphere) (hq : q ∈ closure B) : -q ∈ closure A := by
    have h := mem_image_of_mem (Homeomorph.neg UnitThreeSphere) hq
    rw [(Homeomorph.neg UnitThreeSphere).image_closure] at h
    have he : (Homeomorph.neg UnitThreeSphere) '' B = A := by
      change Neg.neg '' (Neg.neg '' A) = A
      simp only [image_image, neg_neg, image_id']
    rwa [he] at h
  have identify {G H : Set UnitThreeSphere} (hfront' : frontier K = G ∪ H)
      (hG : G ⊆ closure A) (hH : H ⊆ closure B) :
      frontier A = G ∧ frontier B = H := by
    refine ⟨frontier_of_disjoint_exterior_closures hK hA hdis hcover hfront' hG hH, ?_⟩
    apply frontier_of_disjoint_exterior_closures hK hB hdis.symm
      ((union_comm B A).trans hcover) ((hfront'.trans (union_comm G H))) hH hG
  rcases hside with hs | hs
  · have hns : range (fun q => -F q) ⊆ closure B := by
      rintro _ ⟨q, rfl⟩
      exact hnegA _ (hs (mem_range_self q))
    obtain ⟨hfa, hfb⟩ := identify hfront hs hns
    exact ⟨F, hF, hnegF, hmem, hlift, hfa, hfb⟩
  · have hns : range (fun q => -F q) ⊆ closure A := by
      rintro _ ⟨q, rfl⟩
      exact hnegB _ (hs (mem_range_self q))
    obtain ⟨hfa, hfb⟩ := identify (hfront.trans (union_comm _ _)) hns hs
    refine ⟨fun q => -F q, hnegF, ?_, ?_, ?_, hfa, ?_⟩
    · simpa only [neg_neg] using hF
    · intro q
      exact (PuncturedProjectiveSphere.antipode ⟨F q, hmem q⟩).property
    · intro q
      have hn := (PuncturedProjectiveSphere.antipode ⟨F q, hmem q⟩).property
      exact ((S.fibers (-F q) (F q) hn (hmem q)).mpr (Or.inr rfl)).trans (hlift q)
    · simpa only [neg_neg] using hfb

end CapCertificate
end PoincareConjecture
