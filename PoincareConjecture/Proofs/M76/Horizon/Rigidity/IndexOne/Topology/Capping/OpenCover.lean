import PoincareConjecture.Proofs.M54.Mathlib.VanKampenSurjectivity
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.HomotopyFundamentalGroup









set_option autoImplicit false
open Set
open scoped unitInterval

namespace PoincareConjecture.M76.HamiltonIntervalTorus

open VanKampen

set_option backward.isDefEq.respectTransparency false in


theorem pathClass_surjective_of_pathConnected_overlap
    {X : Type*} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (hVs : IsSimplyConnected V) (hW : IsPathConnected (U ∩ V))
    (b : U) (hb : b.1 ∈ V) (x y : U) (q : Path.Homotopic.Quotient x.1 y.1) :
    ∃ p : Path.Homotopic.Quotient x y, p.map (inclusion U) = q := by
  classical
  let c := connector U V hcover hVs b hb
  let P : ∀ {x y : X}, Path.Homotopic.Quotient x y → Prop := fun {x y} p =>
    ∃ r : Path.Homotopic.Quotient (anchor U b x) (anchor U b y),
      p = (Path.Homotopic.Quotient.mk (c x)).symm.trans
        ((r.map (inclusion U)).trans (Path.Homotopic.Quotient.mk (c y)))
  have hgen : ∀ {a d : X} (p : Path.Homotopic.Quotient a d), P p := by
    intro a d p
    refine Path.homotopicQuotient_induction_of_open_cover (cover U V)
      (cover_open U V hU hV) (eq_univ_of_univ_subset (cover_covers U V hcover))
      P ?_ ?_ ?_ p
    · intro a
      refine ⟨Path.Homotopic.Quotient.refl (anchor U b a), ?_⟩
      simp only [Path.Homotopic.Quotient.map_refl, Path.Homotopic.Quotient.refl_trans,
        Path.Homotopic.Quotient.symm_trans]
    · intro a d e p q hp hq
      obtain ⟨p', hp⟩ := hp
      obtain ⟨q', hq⟩ := hq
      refine ⟨p'.trans q', ?_⟩
      rw [hp, hq, Path.Homotopic.Quotient.map_trans]
      simp only [Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.trans_symm_assoc]
    · intro a d p i hp
      cases i with
      | false =>
        change ∀ t, p t ∈ U at hp
        have ha : a ∈ U := by simpa using hp 0
        have hd : d ∈ U := by simpa using hp 1
        let pU : Path (anchor U b a) (anchor U b d) :=
          ⟨⟨fun t => ⟨p t, hp t⟩, p.continuous.subtype_mk hp⟩,
            Subtype.ext (by simpa only [anchor_of_mem U b a ha] using p.source),
            Subtype.ext (by simpa only [anchor_of_mem U b d hd] using p.target)⟩
        refine ⟨Path.Homotopic.Quotient.mk pU, ?_⟩
        exact (Path.Homotopic.Quotient.eq.mpr
          (Path.Homotopic.of_constant_connectors (c a) (c d) (pU.map (inclusion U).continuous) p
            (connector_apply_of_mem U V hcover hVs b hb a ha)
            (connector_apply_of_mem U V hcover hVs b hb d hd) (fun _ => rfl))).symm
      | true =>
        change ∀ t, p t ∈ V at hp
        have ha : a ∈ V := by simpa using hp 0
        have hd : d ∈ V := by simpa using hp 1
        let : PathConnectedSpace ↥(U ∩ V) := isPathConnected_iff_pathConnectedSpace.mp hW
        let pW := PathConnectedSpace.somePath
          (⟨(anchor U b a).1, (anchor U b a).2, anchor_mem_right U V b hb a ha⟩ : ↥(U ∩ V))
          ⟨(anchor U b d).1, (anchor U b d).2, anchor_mem_right U V b hb d hd⟩
        let pU : Path (anchor U b a) (anchor U b d) :=
          pW.map (overlapInclusion U V).continuous
        let r := (c a).symm.trans ((pU.map (inclusion U).continuous).trans (c d))
        have hrange : Set.range r ⊆ V := by
          rw [Path.trans_range, Path.trans_range, Path.symm_range]
          exact union_subset
            (range_subset_iff.mpr (connector_mem_right U V hcover hVs b hb a ha))
            (union_subset (range_subset_iff.mpr (fun t => (pW t).2.2))
              (range_subset_iff.mpr (connector_mem_right U V hcover hVs b hb d hd)))
        refine ⟨Path.Homotopic.Quotient.mk pU, ?_⟩
        exact Path.Homotopic.Quotient.eq.mpr
          (hVs.paths_homotopic_of_mem p r hp (range_subset_iff.mp hrange))
  obtain ⟨r, hr⟩ := hgen q
  obtain ⟨r, rfl⟩ := Path.Homotopic.Quotient.mk_surjective r
  let r' : Path x y := r.cast (anchor_of_mem U b x.1 x.2).symm (anchor_of_mem U b y.1 y.2).symm
  refine ⟨Path.Homotopic.Quotient.mk r', ?_⟩
  have h := Path.Homotopic.of_constant_connectors (c x.1) (c y.1)
    (r.map (inclusion U).continuous) (r'.map (inclusion U).continuous)
    (connector_apply_of_mem U V hcover hVs b hb x.1 x.2)
    (connector_apply_of_mem U V hcover hVs b hb y.1 y.2) (fun _ => rfl)
  exact (hr.trans (Path.Homotopic.Quotient.eq.mpr h)).symm



theorem inclusion_surjective_of_pathConnected_overlap
    {X : Type*} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (hVs : IsSimplyConnected V) (hW : IsPathConnected (U ∩ V))
    (b : U) (hb : b.1 ∈ V) :
    Function.Surjective (FundamentalGroup.map (inclusion U) b) :=
  fun q => pathClass_surjective_of_pathConnected_overlap U V hU hV hcover hVs hW b hb b b q



theorem simplyConnectedSpace_of_open_cover_capping
    {X : Type*} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (hUp : IsPathConnected U) (hVs : IsSimplyConnected V)
    (hW : IsPathConnected (U ∩ V)) (b : ↥(U ∩ V))
    (hgenerate : Function.Surjective (FundamentalGroup.map
      (ContinuousMap.inclusion (inter_subset_left : U ∩ V ⊆ U)) b)) :
    SimplyConnectedSpace X := by
  let bU : U := ⟨b, b.property.1⟩
  let bV : V := ⟨b, b.property.2⟩
  let : SimplyConnectedSpace V := hVs
  let : PathConnectedSpace X := pathConnectedSpace_iff_univ.mpr
    (hcover ▸ hUp.union (isPathConnected_iff_pathConnectedSpace.mpr inferInstance) ⟨b, b.property⟩)
  have hsurj := inclusion_surjective_of_pathConnected_overlap U V hU hV hcover hVs hW
    bU b.property.2
  have htrivial (a : FundamentalGroup X (b : X)) : a = 1 := by
    obtain ⟨c, rfl⟩ := hsurj a
    obtain ⟨d, rfl⟩ := hgenerate c
    change FundamentalGroup.map (inclusion U)
      (ContinuousMap.inclusion (inter_subset_left : U ∩ V ⊆ U) b)
      (FundamentalGroup.map (ContinuousMap.inclusion (inter_subset_left : U ∩ V ⊆ U)) b d) = 1
    rw [← FundamentalGroup.map_comp_apply]
    change FundamentalGroup.map ((inclusion V).comp
      (ContinuousMap.inclusion (inter_subset_right : U ∩ V ⊆ V))) b d = 1
    rw [FundamentalGroup.map_comp_apply]
    have hd : FundamentalGroup.map
        (ContinuousMap.inclusion (inter_subset_right : U ∩ V ⊆ V)) b d = 1 :=
      Subsingleton.elim _ _
    rw [hd, map_one]
  let : Subsingleton (FundamentalGroup X (b : X)) :=
    ⟨fun a c => (htrivial a).trans (htrivial c).symm⟩
  apply simply_connected_iff_loops_nullhomotopic.mpr
  refine ⟨inferInstance, fun x p => ?_⟩
  have hx : Subsingleton (FundamentalGroup X x) :=
    (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected (b : X) x).symm.injective.subsingleton
  have hp : (Path.Homotopic.Quotient.mk p : FundamentalGroup X x) =
      Path.Homotopic.Quotient.mk (Path.refl x) := hx.elim _ _
  exact Path.Homotopic.Quotient.eq.mp hp

end PoincareConjecture.M76.HamiltonIntervalTorus
