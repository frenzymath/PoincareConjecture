import PoincareConjecture.Proofs.M54.Mathlib.VanKampenSurjectivity










set_option autoImplicit false

open Set
open scoped unitInterval

namespace VanKampen

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

private theorem mapped_paths_eq (f : C(X, Y)) (S : Set X)
    (hnull : ∀ (x : X) (p : Path x x), (∀ t, p t ∈ S) →
      (p.map f.continuous).Homotopic (Path.refl (f x)))
    {x y : X} (p q : Path x y) (hp : ∀ t, p t ∈ S) (hq : ∀ t, q t ∈ S) :
    (Path.Homotopic.Quotient.mk p).map f = (Path.Homotopic.Quotient.mk q).map f := by
  have hrange : ∀ t, (p.trans q.symm) t ∈ S := by
    apply range_subset_iff.mp
    rw [Path.trans_range, Path.symm_range]
    exact union_subset (range_subset_iff.mpr hp) (range_subset_iff.mpr hq)
  have h := Path.Homotopic.Quotient.eq.mpr (hnull x (p.trans q.symm) hrange)
  change ((Path.Homotopic.Quotient.mk p).trans
    (Path.Homotopic.Quotient.mk q).symm).map f = Path.Homotopic.Quotient.refl (f x) at h
  have h' := congrArg (fun r => r.trans ((Path.Homotopic.Quotient.mk q).map f)) h
  simpa only [Path.Homotopic.Quotient.map_trans, Path.Homotopic.Quotient.map_symm,
    Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.trans_refl, Path.Homotopic.Quotient.refl_trans] using h'

private noncomputable def connectedConnector (U V : Set X) (hcover : U ∪ V = univ)
    (hV : IsPathConnected V) (b : U) (hb : b.1 ∈ V) (x : X) :
    Path (anchor U b x).1 x := by
  classical
  letI : PathConnectedSpace V := isPathConnected_iff_pathConnectedSpace.mp hV
  exact if hx : x ∈ U then
    (Path.refl x).cast (congrArg Subtype.val (anchor_of_mem U b x hx)) rfl
  else
    ((PathConnectedSpace.somePath (⟨b.1, hb⟩ : V)
      ⟨x, (show x ∈ U ∪ V from hcover.symm ▸ mem_univ x).resolve_left hx⟩).map
        continuous_subtype_val).cast (by simp only [anchor, dif_neg hx]) rfl

private theorem connectedConnector_constant (U V : Set X) (hcover : U ∪ V = univ)
    (hV : IsPathConnected V) (b : U) (hb : b.1 ∈ V) (x : X) (hx : x ∈ U)
    (t : unitInterval) : connectedConnector U V hcover hV b hb x t = x := by
  simp only [connectedConnector, dif_pos hx, Path.cast_coe, Path.refl_apply]

private theorem connectedConnector_mem (U V : Set X) (hcover : U ∪ V = univ)
    (hV : IsPathConnected V) (b : U) (hb : b.1 ∈ V) (x : X) (hx : x ∈ V)
    (t : unitInterval) : connectedConnector U V hcover hV b hb x t ∈ V := by
  classical
  by_cases hxU : x ∈ U
  · simpa only [connectedConnector_constant U V hcover hV b hb x hxU t] using hx
  · simp only [connectedConnector, dif_neg hxU, Path.cast_coe, Path.map_coe,
      Function.comp_apply]
    exact Subtype.prop _

set_option backward.isDefEq.respectTransparency false in



theorem map_loops_nullhomotopic_of_open_cover (f : C(X, Y)) (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (hVp : IsPathConnected V) (hW : IsPathConnected (U ∩ V))
    (hUnull : ∀ (x : X) (p : Path x x), (∀ t, p t ∈ U) →
      (p.map f.continuous).Homotopic (Path.refl (f x)))
    (hVnull : ∀ (x : X) (p : Path x x), (∀ t, p t ∈ V) →
      (p.map f.continuous).Homotopic (Path.refl (f x)))
    (x : X) (p : Path x x) :
    (p.map f.continuous).Homotopic (Path.refl (f x)) := by
  classical
  obtain ⟨b, hbU, hbV⟩ := hW.nonempty
  let bU : U := ⟨b, hbU⟩
  let c := connectedConnector U V hcover hVp bU hbV
  let P : ∀ {a d : X}, Path.Homotopic.Quotient a d → Prop := fun {a d} q =>
    ∃ r : Path.Homotopic.Quotient (anchor U bU a) (anchor U bU d),
      q.map f = ((Path.Homotopic.Quotient.mk (c a)).map f).symm.trans
        (((r.map (inclusion U)).map f).trans ((Path.Homotopic.Quotient.mk (c d)).map f))
  have hgen : ∀ {a d : X} (q : Path.Homotopic.Quotient a d), P q := by
    intro a d q
    refine Path.homotopicQuotient_induction_of_open_cover (cover U V)
      (cover_open U V hU hV) (eq_univ_of_univ_subset (cover_covers U V hcover))
      P ?_ ?_ ?_ q
    · intro a
      refine ⟨Path.Homotopic.Quotient.refl (anchor U bU a), ?_⟩
      simp only [Path.Homotopic.Quotient.map_refl, Path.Homotopic.Quotient.refl_trans,
        Path.Homotopic.Quotient.symm_trans]
    · intro a d e q r hq hr
      obtain ⟨q', hq⟩ := hq
      obtain ⟨r', hr⟩ := hr
      refine ⟨q'.trans r', ?_⟩
      rw [Path.Homotopic.Quotient.map_trans, hq, hr]
      simp only [Path.Homotopic.Quotient.map_trans, Path.Homotopic.Quotient.trans_assoc,
        Path.Homotopic.Quotient.trans_symm_assoc]
    · intro a d q i hq
      cases i with
      | false =>
        change ∀ t, q t ∈ U at hq
        have ha : a ∈ U := by simpa using hq 0
        have hd : d ∈ U := by simpa using hq 1
        let qU : Path (anchor U bU a) (anchor U bU d) :=
          ⟨⟨fun t => ⟨q t, hq t⟩, q.continuous.subtype_mk hq⟩,
            Subtype.ext (by simpa only [anchor_of_mem U bU a ha] using q.source),
            Subtype.ext (by simpa only [anchor_of_mem U bU d hd] using q.target)⟩
        refine ⟨Path.Homotopic.Quotient.mk qU, ?_⟩
        have h := Path.Homotopic.Quotient.eq.mpr
          (Path.Homotopic.of_constant_connectors (c a) (c d)
            (qU.map (inclusion U).continuous) q
            (connectedConnector_constant U V hcover hVp bU hbV a ha)
            (connectedConnector_constant U V hcover hVp bU hbV d hd) (fun _ => rfl))
        have hm := congrArg (fun r => r.map f) h.symm
        change (Path.Homotopic.Quotient.mk q).map f =
          ((Path.Homotopic.Quotient.mk (c a)).symm.trans
            (((Path.Homotopic.Quotient.mk qU).map (inclusion U)).trans
              (Path.Homotopic.Quotient.mk (c d)))).map f at hm
        simpa only [Path.Homotopic.Quotient.map_trans,
          Path.Homotopic.Quotient.map_symm] using hm
      | true =>
        change ∀ t, q t ∈ V at hq
        have ha : a ∈ V := by simpa using hq 0
        have hd : d ∈ V := by simpa using hq 1
        letI : PathConnectedSpace (U ∩ V : Set X) :=
          isPathConnected_iff_pathConnectedSpace.mp hW
        let qW := PathConnectedSpace.somePath
          (⟨(anchor U bU a).1, (anchor U bU a).2,
            anchor_mem_right U V bU hbV a ha⟩ : (U ∩ V : Set X))
          ⟨(anchor U bU d).1, (anchor U bU d).2, anchor_mem_right U V bU hbV d hd⟩
        let qU := qW.map (overlapInclusion U V).continuous
        let r := (c a).symm.trans ((qU.map (inclusion U).continuous).trans (c d))
        have hrange : Set.range r ⊆ V := by
          rw [Path.trans_range, Path.trans_range, Path.symm_range]
          exact union_subset
            (range_subset_iff.mpr (connectedConnector_mem U V hcover hVp bU hbV a ha))
            (union_subset (range_subset_iff.mpr (fun t => (qW t).2.2))
              (range_subset_iff.mpr (connectedConnector_mem U V hcover hVp bU hbV d hd)))
        refine ⟨Path.Homotopic.Quotient.mk qU, ?_⟩
        have hm := mapped_paths_eq f V hVnull q r hq (range_subset_iff.mp hrange)
        change (Path.Homotopic.Quotient.mk q).map f =
          ((Path.Homotopic.Quotient.mk (c a)).symm.trans
            (((Path.Homotopic.Quotient.mk qU).map (inclusion U)).trans
              (Path.Homotopic.Quotient.mk (c d)))).map f at hm
        simpa only [Path.Homotopic.Quotient.map_trans,
          Path.Homotopic.Quotient.map_symm] using hm
  obtain ⟨r, hr⟩ := hgen (Path.Homotopic.Quotient.mk p)
  obtain ⟨r, rfl⟩ := Path.Homotopic.Quotient.mk_surjective r
  have hnull := Path.Homotopic.Quotient.eq.mpr
    (hUnull (anchor U bU x).1 (r.map (inclusion U).continuous) (fun t => (r t).2))
  change ((Path.Homotopic.Quotient.mk r).map (inclusion U)).map f =
    Path.Homotopic.Quotient.refl (f (anchor U bU x).1) at hnull
  apply Path.Homotopic.Quotient.eq.mp
  change (Path.Homotopic.Quotient.mk p).map f = Path.Homotopic.Quotient.refl (f x)
  change (Path.Homotopic.Quotient.mk p).map f = _ at hr
  rw [hr, hnull]
  change ((Path.Homotopic.Quotient.mk (c x)).map f).symm.trans
    ((Path.Homotopic.Quotient.refl (f (anchor U bU x).1)).trans
      ((Path.Homotopic.Quotient.mk (c x)).map f)) = _
  simp only [Path.Homotopic.Quotient.refl_trans, Path.Homotopic.Quotient.symm_trans]

end VanKampen
