import PoincareConjecture.Proofs.M54.Mathlib.VanKampenSurjectivity

set_option autoImplicit false

open Set
open scoped unitInterval

namespace VanKampen

variable {X : Type*} [TopologicalSpace X] (U V : Set X)

noncomputable def adaptedTails (hW : IsSimplyConnected (U ∩ V))
    (w b : U) (hw : w.1 ∈ V) (x : U) (hx : Joined b x) :
    Path.Homotopic.Quotient b x := by
  classical
  exact if hbw : Joined b w then
    (Path.Homotopic.Quotient.mk hbw.somePath).trans
      (overlapTails U V hW w hw x (hbw.symm.trans hx))
  else Path.Homotopic.Quotient.mk hx.somePath

set_option backward.isDefEq.respectTransparency false in

theorem adapted_transport_eq_one (hW : IsSimplyConnected (U ∩ V))
    (w b : U) (hw : w.1 ∈ V) (p : C(unitInterval, U))
    (hp : ∀ t, (p t).1 ∈ V) :
    Path.Homotopic.Quotient.basedContinuousTransport b
      (adaptedTails U V hW w b hw) p = 1 := by
  classical
  let : SimplyConnectedSpace (U ∩ V : Set X) := hW
  have hw0 : Joined w (p 0) :=
    ⟨(PathConnectedSpace.somePath (⟨w.1, w.2, hw⟩ : (U ∩ V : Set X))
      ⟨(p 0).1, (p 0).2, hp 0⟩).map (overlapInclusion U V).continuous⟩
  have hw1 : Joined w (p 1) := hw0.trans ⟨p.toPath⟩
  by_cases hbw : Joined b w
  · rw [Path.Homotopic.Quotient.basedContinuousTransport,
      Path.Homotopic.Quotient.basedTransport_of_joined b _ _
        (hbw.trans hw0) (hbw.trans hw1)]
    simp only [adaptedTails, dif_pos hbw]
    have h := overlap_transport_eq_one U V hW w hw p hp
    rw [Path.Homotopic.Quotient.basedContinuousTransport,
      Path.Homotopic.Quotient.basedTransport_of_joined w _ _ hw0 hw1] at h
    have h' : (overlapTails U V hW w hw (p 0) hw0).trans
        ((Path.Homotopic.Quotient.mk p.toPath).trans
          (overlapTails U V hW w hw (p 1) hw1).symm) =
        Path.Homotopic.Quotient.refl w := congrArg MulOpposite.unop h
    apply MulOpposite.unop_injective
    change ((Path.Homotopic.Quotient.mk hbw.somePath).trans _).trans
      ((Path.Homotopic.Quotient.mk p.toPath).trans
        ((Path.Homotopic.Quotient.mk hbw.somePath).trans _).symm) =
      Path.Homotopic.Quotient.refl b
    have hrev {a c d : U} (r : Path.Homotopic.Quotient a c)
        (s : Path.Homotopic.Quotient c d) : (r.trans s).symm = s.symm.trans r.symm := by
      induction r using Path.Homotopic.Quotient.ind with
      | mk r =>
        induction s using Path.Homotopic.Quotient.ind with
        | mk s => exact congrArg Path.Homotopic.Quotient.mk (Path.trans_symm r s)
    rw [hrev]
    simp only [Path.Homotopic.Quotient.trans_assoc]
    rw [← Path.Homotopic.Quotient.trans_assoc (Path.Homotopic.Quotient.mk p.toPath),
      ← Path.Homotopic.Quotient.trans_assoc (overlapTails U V hW w hw (p 0) hw0), h']
    simp only [Path.Homotopic.Quotient.refl_trans, Path.Homotopic.Quotient.trans_symm]
  · apply Path.Homotopic.Quotient.basedTransport_of_not_joined
    exact fun hb0 => hbw (hb0.trans hw0.symm)

variable (b : U)
    (tails : ∀ x : U, Joined b x → Path.Homotopic.Quotient b x)
    (htails : ∀ (p : C(unitInterval, U)), (∀ t, (p t).1 ∈ V) →
      Path.Homotopic.Quotient.basedContinuousTransport b tails p = 1)

noncomputable def transportOfTails :
    LocalPathTransport (cover U V) (FundamentalGroup U b)ᵐᵒᵖ := by
  classical
  let val (p : C(unitInterval, X)) : (FundamentalGroup U b)ᵐᵒᵖ :=
    if hp : ∀ t, p t ∈ U then
      Path.Homotopic.Quotient.basedContinuousTransport b tails (p.restrictRange U hp)
    else 1
  have hfirst (p : C(unitInterval, X)) (hp : ∀ t, p t ∈ U) :
      val p = Path.Homotopic.Quotient.basedContinuousTransport b tails
        (p.restrictRange U hp) := by simp only [val, dif_pos hp]
  have hsecond (p : C(unitInterval, X)) (hp : ∀ t, p t ∈ V) : val p = 1 := by
    by_cases hpU : ∀ t, p t ∈ U
    · rw [hfirst p hpU]
      exact htails _ hp
    · simp only [val, dif_neg hpU]
  refine ⟨val, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ U
    · rw [hfirst _ (fun _ => hx)]
      exact Path.Homotopic.Quotient.basedContinuousTransport_const b tails ⟨x, hx⟩
    · exact dif_neg (fun h => hx (h 0))
  · intro H i hH
    cases i with
    | false =>
      have hU : ∀ z, H z ∈ U := hH
      rw [hfirst _ (fun t => hU (t, 0)), hfirst _ (fun t => hU (1, t)),
        hfirst _ (fun t => hU (0, t)), hfirst _ (fun t => hU (t, 1))]
      exact Path.Homotopic.Quotient.basedContinuousTransport_square b tails (H.restrictRange U hU)
    | true =>
      have hV : ∀ z, H z ∈ V := hH
      rw [hsecond _ (fun t => hV (t, 0)), hsecond _ (fun t => hV (1, t)),
        hsecond _ (fun t => hV (0, t)), hsecond _ (fun t => hV (t, 1))]

set_option backward.isDefEq.respectTransparency false in

theorem transportOfTails_restriction (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = univ) :
    (((transportOfTails U V b tails htails).global (cover_open U V hU hV)
      (cover_covers U V hcover)).toMonoidHom b.1).comp
      (FundamentalGroup.map (inclusion U) b) =
      (MulAut.conj (G := FundamentalGroup U b) (tails b (Joined.refl b))⁻¹).toMonoidHom := by
  classical
  ext q
  induction q using Path.Homotopic.Quotient.ind with
  | mk p =>
    let L := transportOfTails U V b tails htails
    change MulOpposite.unop (L.extend (cover_open U V hU hV) (cover_covers U V hcover)
      (p.map (inclusion U).continuous).toContinuousMap) = _
    rw [L.extend_eq_local (cover_open U V hU hV) (cover_covers U V hcover) _ false
      (fun t => (p t).2)]
    change MulOpposite.unop (if hp : ∀ t, (p.map (inclusion U).continuous) t ∈ U then
      Path.Homotopic.Quotient.basedContinuousTransport b tails
        ((p.map (inclusion U).continuous).toContinuousMap.restrictRange U hp) else 1) = _
    have hpU : ∀ t, (p.map (inclusion U).continuous) t ∈ U := fun t => (p t).2
    rw [dif_pos hpU]
    have hp : (p.map (inclusion U).continuous).toContinuousMap.restrictRange U
        (fun t => (p t).2) = p.toContinuousMap := by ext t; rfl
    rw [hp, Path.Homotopic.Quotient.basedContinuousTransport_path,
      Path.Homotopic.Quotient.basedTransport_of_joined b tails _ (Joined.refl b) (Joined.refl b)]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rfl

omit tails htails in
set_option backward.isDefEq.respectTransparency false in

theorem exists_retraction (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (hW : IsSimplyConnected (U ∩ V)) :
    ∃ r : FundamentalGroup X b.1 →* FundamentalGroup U b,
      r.comp (FundamentalGroup.map (inclusion U) b) = MonoidHom.id _ := by
  obtain ⟨w, hwU, hwV⟩ := hW.nonempty
  let tails := adaptedTails U V hW ⟨w, hwU⟩ b hwV
  let ht := adapted_transport_eq_one U V hW ⟨w, hwU⟩ b hwV
  let L := transportOfTails U V b tails ht
  let e := MulAut.conj (G := FundamentalGroup U b) (tails b (Joined.refl b))⁻¹
  refine ⟨e.symm.toMonoidHom.comp
    ((L.global (cover_open U V hU hV) (cover_covers U V hcover)).toMonoidHom b.1), ?_⟩
  rw [MonoidHom.comp_assoc, transportOfTails_restriction U V b tails ht hU hV hcover]
  ext q
  exact e.symm_apply_apply q

omit tails htails in

theorem inclusion_injective_at (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (hW : IsSimplyConnected (U ∩ V)) :
    Function.Injective (FundamentalGroup.map (inclusion U) b) := by
  obtain ⟨r, hr⟩ := exists_retraction U V b hU hV hcover hW
  exact (show Function.LeftInverse r (FundamentalGroup.map (inclusion U) b) from
    fun q => DFunLike.congr_fun hr q).injective

omit tails htails in

noncomputable def inclusionMulEquivAt (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = univ) (hVs : IsSimplyConnected V)
    (hW : IsSimplyConnected (U ∩ V)) : FundamentalGroup U b ≃* FundamentalGroup X b.1 := by
  let w := hW.nonempty.choose
  have hwU : w ∈ U := hW.nonempty.choose_spec.1
  have hwV : w ∈ V := hW.nonempty.choose_spec.2
  exact MulEquiv.ofBijective (FundamentalGroup.map (inclusion U) b)
    ⟨inclusion_injective_at U V b hU hV hcover hW,
      fun q => pathClass_surjective U V hU hV hcover hVs hW ⟨w, hwU⟩ hwV b b q⟩

end VanKampen
