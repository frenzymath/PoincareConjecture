import PoincareConjecture.Proofs.M54.Mathlib.VanKampenRetraction

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped unitInterval

namespace VanKampen

variable {X G : Type*} [TopologicalSpace X] [Group G]
  (U V : Set X) (hUV : IsSimplyConnected (U ∩ V))
  (b : U) (hb : b.1 ∈ V)

private def secondBase {U : Set X} (V : Set X) (b : U) (hb : b.1 ∈ V) : V := ⟨b.1, hb⟩

private noncomputable def combinedTransport
    (f : FundamentalGroup U b →* G)
    (g : FundamentalGroup V (secondBase V b hb) →* G) :
    LocalPathTransport (cover U V) Gᵐᵒᵖ where
  value p := f.op ((localTransport U V hUV b hb).value p) *
    g.op ((localTransport V U (inter_comm U V ▸ hUV) (secondBase V b hb) b.2).value p)
  map_const x := by simp only [LocalPathTransport.map_const, map_one, one_mul]
  square H i hH := by
    cases i with
    | false =>
      have hU : ∀ z, H z ∈ U := hH
      simp only [localTransport,
        localValue_second V U _ _ _ (H.horizontalPath 0) (fun t => hU (t, 0)),
        localValue_second V U _ _ _ (H.verticalPath 1) (fun t => hU (1, t)),
        localValue_second V U _ _ _ (H.verticalPath 0) (fun t => hU (0, t)),
        localValue_second V U _ _ _ (H.horizontalPath 1) (fun t => hU (t, 1)), map_one, mul_one]
      exact (map_mul f.op _ _).symm.trans
        ((congrArg f.op ((localTransport U V hUV b hb).square H false hH)).trans
          (map_mul f.op _ _))
    | true =>
      have hV : ∀ z, H z ∈ V := hH
      simp only [localTransport,
        localValue_second U V _ _ _ (H.horizontalPath 0) (fun t => hV (t, 0)),
        localValue_second U V _ _ _ (H.verticalPath 1) (fun t => hV (1, t)),
        localValue_second U V _ _ _ (H.verticalPath 0) (fun t => hV (0, t)),
        localValue_second U V _ _ _ (H.horizontalPath 1) (fun t => hV (t, 1)), map_one, one_mul]
      exact (map_mul g.op _ _).symm.trans
        ((congrArg g.op ((localTransport V U (inter_comm U V ▸ hUV)
          (secondBase V b hb) b.2).square H false hH)).trans (map_mul g.op _ _))

variable (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
  (f : FundamentalGroup U b →* G)
  (g : FundamentalGroup V (secondBase V b hb) →* G)

private noncomputable def combinedHom : FundamentalGroup X b.1 →* G :=
  ((combinedTransport U V hUV b hb f g).global (cover_open U V hU hV)
    (cover_covers U V hcover)).toMonoidHom b.1

private theorem combinedHom_first (a : FundamentalGroup U b) :
    combinedHom U V hUV b hb hU hV hcover f g (FundamentalGroup.map (inclusion U) b a) =
      f (preliminaryRetraction U V hU hV hcover hUV b hb
        (FundamentalGroup.map (inclusion U) b a)) := by
  induction a using Path.Homotopic.Quotient.ind with
  | mk a =>
    change MulOpposite.unop ((combinedTransport U V hUV b hb f g).extend _ _
      (a.map (inclusion U).continuous).toContinuousMap) =
        f (MulOpposite.unop ((localTransport U V hUV b hb).extend _ _
          (a.map (inclusion U).continuous).toContinuousMap))
    rw [LocalPathTransport.extend_eq_local _ _ _ _ false (fun t => (a t).2),
      LocalPathTransport.extend_eq_local _ _ _ _ false (fun t => (a t).2)]
    simp only [combinedTransport, localTransport,
      localValue_second V U _ _ _ (a.map (inclusion U).continuous).toContinuousMap
        (fun t => (a t).2), map_one, mul_one]
    rfl

private theorem combinedHom_second (a : FundamentalGroup V (secondBase V b hb)) :
    combinedHom U V hUV b hb hU hV hcover f g
      (FundamentalGroup.map (inclusion V) (secondBase V b hb) a) =
      g (preliminaryRetraction V U hV hU (union_comm U V ▸ hcover)
        (inter_comm U V ▸ hUV) (secondBase V b hb) b.2
          (FundamentalGroup.map (inclusion V) (secondBase V b hb) a)) := by
  induction a using Path.Homotopic.Quotient.ind with
  | mk a =>
    change MulOpposite.unop ((combinedTransport U V hUV b hb f g).extend _ _
      (a.map (inclusion V).continuous).toContinuousMap) =
        g (MulOpposite.unop ((localTransport V U (inter_comm U V ▸ hUV)
          (secondBase V b hb) b.2).extend _ _
            (a.map (inclusion V).continuous).toContinuousMap))
    rw [LocalPathTransport.extend_eq_local _ _ _ _ true (fun t => (a t).2),
      LocalPathTransport.extend_eq_local _ _ _ _ false (fun t => (a t).2)]
    simp only [combinedTransport, localTransport,
      localValue_second U V _ _ _ (a.map (inclusion V).continuous).toContinuousMap
        (fun t => (a t).2), map_one, one_mul]
    rfl

include hUV hb hU hV hcover in

theorem exists_hom_range_contains :
    ∃ φ : FundamentalGroup X b.1 →* G,
      f.range ≤ φ.range ∧ g.range ≤ φ.range := by
  refine ⟨combinedHom U V hUV b hb hU hV hcover f g, ?_, ?_⟩
  · rintro z ⟨a, rfl⟩
    let e := MulAut.conj (G := FundamentalGroup U b) (basepointLoop U V hUV b hb)⁻¹
    refine ⟨FundamentalGroup.map (inclusion U) b (e.symm a), ?_⟩
    rw [combinedHom_first]
    have he := DFunLike.congr_fun
      (preliminaryRetraction_comp_inclusion U V hU hV hcover hUV b hb) (e.symm a)
    change preliminaryRetraction U V hU hV hcover hUV b hb
      (FundamentalGroup.map (inclusion U) b (e.symm a)) = e (e.symm a) at he
    rw [he, e.apply_symm_apply]
  · rintro z ⟨a, rfl⟩
    let e := MulAut.conj (G := FundamentalGroup V (secondBase V b hb))
      (basepointLoop V U (inter_comm U V ▸ hUV) (secondBase V b hb) b.2)⁻¹
    refine ⟨FundamentalGroup.map (inclusion V) (secondBase V b hb) (e.symm a), ?_⟩
    rw [combinedHom_second]
    have he := DFunLike.congr_fun
      (preliminaryRetraction_comp_inclusion V U hV hU (union_comm U V ▸ hcover)
        (inter_comm U V ▸ hUV) (secondBase V b hb) b.2) (e.symm a)
    change preliminaryRetraction V U hV hU (union_comm U V ▸ hcover)
      (inter_comm U V ▸ hUV) (secondBase V b hb) b.2
      (FundamentalGroup.map (inclusion V) (secondBase V b hb) (e.symm a)) =
        e (e.symm a) at he
    rw [he, e.apply_symm_apply]

end VanKampen
