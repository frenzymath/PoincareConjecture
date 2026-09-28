import PoincareConjecture.Proofs.M54.Mathlib.VanKampenRetraction
import PoincareConjecture.Proofs.M54.Mathlib.PathMaps











set_option autoImplicit false

open Set
open scoped unitInterval

namespace VanKampen

variable {X : Type*} [TopologicalSpace X] (U V : Set X)



noncomputable def anchor (b : U) (x : X) : U := by
  classical
  exact if hx : x ∈ U then ⟨x, hx⟩ else b

omit [TopologicalSpace X] in


theorem anchor_of_mem (b : U) (x : X) (hx : x ∈ U) : anchor U b x = ⟨x, hx⟩ := by
  simp only [anchor, dif_pos hx]

omit [TopologicalSpace X] in


theorem anchor_mem_right (b : U) (hb : b.1 ∈ V) (x : X) (hx : x ∈ V) :
    (anchor U b x).1 ∈ V := by
  classical
  by_cases hxU : x ∈ U
  · simpa only [anchor, dif_pos hxU] using hx
  · simpa only [anchor, dif_neg hxU] using hb

omit [TopologicalSpace X] in
private theorem right_of_not_left (hcover : U ∪ V = univ) (x : X) (hx : x ∉ U) :
    x ∈ V := (show x ∈ U ∪ V from hcover.symm ▸ mem_univ x).resolve_left hx



noncomputable def connector (hcover : U ∪ V = univ) (hV : IsSimplyConnected V)
    (b : U) (hb : b.1 ∈ V) (x : X) : Path (anchor U b x).1 x := by
  classical
  let : SimplyConnectedSpace V := hV
  exact if hx : x ∈ U then
    (Path.refl x).cast (congrArg Subtype.val (anchor_of_mem U b x hx)) rfl
  else
    ((PathConnectedSpace.somePath (⟨b.1, hb⟩ : V)
      ⟨x, right_of_not_left U V hcover x hx⟩).map continuous_subtype_val).cast
        (by simp only [anchor, dif_neg hx]) rfl



theorem connector_apply_of_mem (hcover : U ∪ V = univ) (hV : IsSimplyConnected V)
    (b : U) (hb : b.1 ∈ V) (x : X) (hx : x ∈ U) (t : unitInterval) :
    connector U V hcover hV b hb x t = x := by
  simp only [connector, dif_pos hx, Path.cast_coe, Path.refl_apply]



theorem connector_mem_right (hcover : U ∪ V = univ) (hV : IsSimplyConnected V)
    (b : U) (hb : b.1 ∈ V) (x : X) (hx : x ∈ V) (t : unitInterval) :
    connector U V hcover hV b hb x t ∈ V := by
  classical
  by_cases hxU : x ∈ U
  · simpa only [connector_apply_of_mem U V hcover hV b hb x hxU t] using hx
  · simp only [connector, dif_neg hxU, Path.cast_coe, Path.map_coe, Function.comp_apply]
    exact Subtype.prop _

set_option backward.isDefEq.respectTransparency false in



theorem pathClass_surjective (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (hVs : IsSimplyConnected V) (hW : IsSimplyConnected (U ∩ V))
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
        let : SimplyConnectedSpace (U ∩ V : Set X) := hW
        let pW := PathConnectedSpace.somePath
          (⟨(anchor U b a).1, (anchor U b a).2, anchor_mem_right U V b hb a ha⟩ :
            (U ∩ V : Set X))
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




theorem inclusion_surjective (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (hVs : IsSimplyConnected V) (hW : IsSimplyConnected (U ∩ V))
    (b : U) (hb : b.1 ∈ V) :
    Function.Surjective (FundamentalGroup.map (inclusion U) b) :=
  fun q => pathClass_surjective U V hU hV hcover hVs hW b hb b b q



noncomputable def inclusionMulEquiv (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (hVs : IsSimplyConnected V) (hW : IsSimplyConnected (U ∩ V))
    (b : U) (hb : b.1 ∈ V) : FundamentalGroup U b ≃* FundamentalGroup X b.1 :=
  MulEquiv.ofBijective (FundamentalGroup.map (inclusion U) b)
    ⟨inclusion_injective U V hU hV hcover hW b hb,
      inclusion_surjective U V hU hV hcover hVs hW b hb⟩

end VanKampen
