import PoincareConjecture.Proofs.M38.ProjectiveDoubleBoundary

set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

namespace PoincareConjecture.M38

variable {Q : Type*} [TopologicalSpace Q]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Q]
  {p : RealProjectiveThree} {U : Set Q}

theorem puncturedProjective_quotient :
    IsQuotientMap ({q : RealProjectiveThree | q ≠ p}.restrictPreimage
      (Quotient.mk' : UnitThreeSphere → RealProjectiveThree)) := by
  let : T2Space RealProjectiveThree := projective_t2
  exact projective_open_quotient.isQuotientMap.restrictPreimage_isOpen
    (isOpen_ne_fun continuous_id continuous_const)

theorem puncturedProjectiveCover_quotient
    (C : StandardPuncturedProjectiveCover Q p U) :
    IsQuotientMap (fun x : {x : UnitThreeSphere // Quotient.mk' x ≠ p} =>
      (⟨C.cover x.1, C.image_eq.subset (Set.mem_image_of_mem C.cover x.2)⟩ : U)) := by
  let V : Set UnitThreeSphere := {x | Quotient.mk' x ≠ p}
  have hV : IsOpen V := by
    let : T2Space RealProjectiveThree := projective_t2
    exact (isOpen_ne_fun continuous_id continuous_const).preimage continuous_quotient_mk'
  have hlocal := C.local_diffeomorph.isLocalHomeomorphOn
  have hopen : IsOpenMap (fun x : V => C.cover x.1) := by
    apply IsOpenMap.of_nhds_le
    intro x
    rw [show (fun x : V => C.cover x.1) = C.cover ∘ Subtype.val from rfl,
      ← Filter.map_map, hV.isOpenEmbedding_subtypeVal.map_nhds_eq,
      hlocal.map_nhds_eq x.2]
  apply (hopen.codRestrict _).isQuotientMap
    (C.local_diffeomorph.contMDiffOn.continuousOn.domRestrict.subtype_mk _)
  intro y
  obtain ⟨x, hx, he⟩ := C.image_eq.symm.subset y.2
  exact ⟨⟨x, hx⟩, Subtype.ext he⟩

theorem exists_puncturedProjectiveCover_homeomorph
    (C : StandardPuncturedProjectiveCover Q p U) :
    ∃ e : PuncturedRealProjectiveThree p ≃ₜ U,
      ∀ (x : UnitThreeSphere) (hx : Quotient.mk' x ≠ p),
        (e ⟨Quotient.mk' x, hx⟩).1 = C.cover x := by
  let V := {x : UnitThreeSphere // Quotient.mk' x ≠ p}
  let q : V → PuncturedRealProjectiveThree p :=
    fun x => ⟨Quotient.mk' x.1, x.2⟩
  let c : V → U := fun x =>
    ⟨C.cover x.1, C.image_eq.subset (Set.mem_image_of_mem C.cover x.2)⟩
  have hq : IsQuotientMap q := puncturedProjective_quotient
  have hc : IsQuotientMap c := puncturedProjectiveCover_quotient C
  have hfib (x y : V) : c x = c y ↔ q x = q y := by
    change (Subtype.mk (C.cover x.1) _ = Subtype.mk (C.cover y.1) _) ↔
      (Subtype.mk (Quotient.mk' x.1) _ = Subtype.mk (Quotient.mk' y.1) _)
    rw [Subtype.mk.injEq, Subtype.mk.injEq, C.fibers x.1 y.1 x.2 y.2]
    exact (Quotient.eq : (Quotient.mk' x.1 : RealProjectiveThree) = Quotient.mk' y.1 ↔
      x.1 = y.1 ∨ x.1 = -y.1).symm
  let f : PuncturedRealProjectiveThree p → U := c ∘ Function.surjInv hq.surjective
  have hcomp (x : V) : f (q x) = c x := by
    exact (hfib _ x).mpr (Function.surjInv_eq hq.surjective (q x))
  have hfinj : Function.Injective f := by
    intro x y hxy
    have hh := (hfib (Function.surjInv hq.surjective x)
      (Function.surjInv hq.surjective y)).mp hxy
    simpa only [Function.surjInv_eq] using hh
  have hfsurj : Function.Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ := hc.surjective y
    exact ⟨q x, hcomp x⟩
  have hfquot : IsQuotientMap f := by
    apply hq.of_comp_isQuotientMap
    simpa only [show f ∘ q = c from funext hcomp] using hc
  let e := (Equiv.ofBijective f ⟨hfinj, hfsurj⟩).toHomeomorphOfContinuousOpen
    hfquot.continuous ((isHomeomorph_iff_isQuotientMap_injective.mpr
      ⟨hfquot, hfinj⟩).isOpenMap)
  exact ⟨e, fun x hx => congrArg Subtype.val (hcomp ⟨x, hx⟩)⟩

noncomputable def puncturedProjectiveCoverHomeomorph
    (C : StandardPuncturedProjectiveCover Q p U) :
    PuncturedRealProjectiveThree p ≃ₜ U :=
  Classical.choose (exists_puncturedProjectiveCover_homeomorph C)

theorem puncturedProjectiveCoverHomeomorph_apply
    (C : StandardPuncturedProjectiveCover Q p U)
    (x : UnitThreeSphere) (hx : Quotient.mk' x ≠ p) :
    (puncturedProjectiveCoverHomeomorph C ⟨Quotient.mk' x, hx⟩).1 = C.cover x :=
  Classical.choose_spec (exists_puncturedProjectiveCover_homeomorph C) x hx

theorem puncturedProjectiveCover_compact_lift
    (C : StandardPuncturedProjectiveCover Q p U) {K : Set U} (hK : IsCompact K) :
    IsCompact ({x : UnitThreeSphere | Quotient.mk' x ≠ p} ∩
      C.cover ⁻¹' (Subtype.val '' K)) := by
  let : T2Space RealProjectiveThree := projective_t2
  let e := puncturedProjectiveCoverHomeomorph C
  let L : Set RealProjectiveThree := Subtype.val '' (e.symm '' K)
  have hL : IsCompact L :=
    (hK.image e.symm.continuous).image continuous_subtype_val
  have heq : {x : UnitThreeSphere | Quotient.mk' x ≠ p} ∩
      C.cover ⁻¹' (Subtype.val '' K) =
      (Quotient.mk' : UnitThreeSphere → RealProjectiveThree) ⁻¹' L := by
    ext x
    constructor
    · rintro ⟨hx, y, hy, he⟩
      have heq : e ⟨Quotient.mk' x, hx⟩ = y := by
        apply Subtype.ext
        exact (puncturedProjectiveCoverHomeomorph_apply C x hx).trans he.symm
      exact ⟨e.symm y, ⟨y, hy, rfl⟩,
        congrArg Subtype.val (heq ▸ e.symm_apply_apply ⟨Quotient.mk' x, hx⟩)⟩
    · rintro ⟨z, ⟨y, hy, rfl⟩, he⟩
      have hx : Quotient.mk' x ≠ p := he ▸ (e.symm y).2
      have heq : e.symm y = ⟨Quotient.mk' x, hx⟩ := Subtype.ext he
      refine ⟨hx, y, hy, ?_⟩
      rw [← puncturedProjectiveCoverHomeomorph_apply C x hx]
      exact congrArg Subtype.val ((e.apply_symm_apply y).symm.trans (congrArg e heq))
  rw [heq]
  exact (hL.isClosed.preimage continuous_quotient_mk').isCompact

theorem puncturedProjectiveCover_end_neighborhood [CompactSpace Q]
    (C : StandardPuncturedProjectiveCover Q p U) {S O : Set Q}
    (hboundary : closure U ⊆ U ∪ S) (hO : IsOpen O) (hS : S ⊆ O) :
    ∃ W : Set UnitThreeSphere, IsOpen W ∧
      {x : UnitThreeSphere | Quotient.mk' x = p} ⊆ W ∧
      ∀ x ∈ W, Quotient.mk' x ≠ p → C.cover x ∈ O := by
  let K : Set Q := closure U \ O
  have hK : IsCompact K := isClosed_closure.isCompact.diff hO
  have hKU : K ⊆ U := by
    intro y hy
    exact (hboundary hy.1).elim id (fun hs => (hy.2 (hS hs)).elim)
  have hKsub : IsCompact ((Subtype.val : U → Q) ⁻¹' K) :=
    Topology.IsInducing.subtypeVal.isCompact_preimage' hK (by simpa using hKU)
  have himage : Subtype.val '' ((Subtype.val : U → Q) ⁻¹' K) = K := by
    ext y
    exact ⟨fun ⟨z, hz, he⟩ => he ▸ hz, fun hy => ⟨⟨y, hKU hy⟩, hy, rfl⟩⟩
  have hlift := puncturedProjectiveCover_compact_lift C hKsub
  rw [himage] at hlift
  refine ⟨({x : UnitThreeSphere | Quotient.mk' x ≠ p} ∩ C.cover ⁻¹' K)ᶜ,
    hlift.isClosed.isOpen_compl, ?_, ?_⟩
  · intro x hx hmem
    exact hmem.1 hx
  · intro x hx hn
    by_contra hnot
    apply hx
    exact ⟨hn, subset_closure (C.image_eq.subset (Set.mem_image_of_mem C.cover hn)), hnot⟩

theorem projectiveDouble_first_end_neighborhood (C : SmoothProjectiveDoubleModel Q)
    {O : Set Q} (hO : IsOpen O) (hS : C.sphere ⊆ O) :
    ∃ W : Set UnitThreeSphere, IsOpen W ∧
      {x : UnitThreeSphere | Quotient.mk' x = C.first_puncture} ⊆ W ∧
      ∀ x ∈ W, Quotient.mk' x ≠ C.first_puncture → C.first_model.cover x ∈ O := by
  let : CompactSpace Q := isCompact_univ_iff.mp C.compact
  exact puncturedProjectiveCover_end_neighborhood C.first_model
    (by rw [(projectiveDouble_region_closures C).1]) hO hS

theorem projectiveDouble_second_end_neighborhood (C : SmoothProjectiveDoubleModel Q)
    {O : Set Q} (hO : IsOpen O) (hS : C.sphere ⊆ O) :
    ∃ W : Set UnitThreeSphere, IsOpen W ∧
      {x : UnitThreeSphere | Quotient.mk' x = C.second_puncture} ⊆ W ∧
      ∀ x ∈ W, Quotient.mk' x ≠ C.second_puncture → C.second_model.cover x ∈ O := by
  let : CompactSpace Q := isCompact_univ_iff.mp C.compact
  exact puncturedProjectiveCover_end_neighborhood C.second_model
    (by rw [(projectiveDouble_region_closures C).2]) hO hS

end PoincareConjecture.M38
