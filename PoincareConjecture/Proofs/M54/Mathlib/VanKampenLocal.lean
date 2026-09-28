import PoincareConjecture.Proofs.M54.Mathlib.BasedPathTransport
import PoincareConjecture.Proofs.M54.Mathlib.PathTransportFundamentalGroup











set_option autoImplicit false

open Set
open scoped unitInterval

namespace ContinuousMap

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]



def restrictRange (p : C(X, Y)) (U : Set Y) (hp : ∀ x, p x ∈ U) : C(X, U) :=
  ⟨fun x => ⟨p x, hp x⟩, p.continuous.subtype_mk hp⟩



@[simp] theorem restrictRange_apply (p : C(X, Y)) (U : Set Y)
    (hp : ∀ x, p x ∈ U) (x : X) : (p.restrictRange U hp x).1 = p x := rfl

end ContinuousMap

namespace VanKampen

variable {X : Type*} [TopologicalSpace X] (U V : Set X)
    (hUV : IsSimplyConnected (U ∩ V)) (b : U) (hb : b.1 ∈ V)



def overlapInclusion : C((U ∩ V : Set X), U) :=
  ⟨fun x => ⟨x.1, x.2.1⟩, continuous_subtype_val.subtype_mk (fun x => x.2.1)⟩



noncomputable def overlapTails (x : U) (hx : Joined b x) :
    Path.Homotopic.Quotient b x := by
  classical
  let : SimplyConnectedSpace (U ∩ V : Set X) := hUV
  exact if hV : x.1 ∈ V then
    Path.Homotopic.Quotient.mk
      ((PathConnectedSpace.somePath (⟨b.1, b.2, hb⟩ : (U ∩ V : Set X)) ⟨x.1, x.2, hV⟩).map
        (overlapInclusion U V).continuous)
  else Path.Homotopic.Quotient.mk hx.somePath

set_option backward.isDefEq.respectTransparency false in


theorem overlap_transport_eq_one (p : C(unitInterval, U))
    (hp : ∀ t, (p t).1 ∈ V) :
    Path.Homotopic.Quotient.basedContinuousTransport b (overlapTails U V hUV b hb) p = 1 := by
  classical
  let : SimplyConnectedSpace (U ∩ V : Set X) := hUV
  let bW : (U ∩ V : Set X) := ⟨b.1, b.2, hb⟩
  let pW : C(unitInterval, (U ∩ V : Set X)) :=
    ⟨fun t => ⟨(p t).1, (p t).2, hp t⟩, (continuous_subtype_val.comp p.continuous).subtype_mk _⟩
  let a := PathConnectedSpace.somePath bW (pW 0)
  let c := PathConnectedSpace.somePath bW (pW 1)
  have ha : Joined b (p 0) := ⟨a.map (overlapInclusion U V).continuous⟩
  have hc : Joined b (p 1) := ⟨c.map (overlapInclusion U V).continuous⟩
  rw [Path.Homotopic.Quotient.basedContinuousTransport,
    Path.Homotopic.Quotient.basedTransport_of_joined b _ _ ha hc]
  have htail0 : overlapTails U V hUV b hb (p 0) ha =
      Path.Homotopic.Quotient.mk (a.map (overlapInclusion U V).continuous) := by
    simp only [overlapTails, dif_pos (hp 0)]
    rfl
  have htail1 : overlapTails U V hUV b hb (p 1) hc =
      Path.Homotopic.Quotient.mk (c.map (overlapInclusion U V).continuous) := by
    simp only [overlapTails, dif_pos (hp 1)]
    rfl
  rw [htail0, htail1]
  apply MulOpposite.unop_injective
  change (Path.Homotopic.Quotient.mk (a.map (overlapInclusion U V).continuous)).trans
      ((Path.Homotopic.Quotient.mk p.toPath).trans
        (Path.Homotopic.Quotient.mk (c.map (overlapInclusion U V).continuous)).symm) =
    Path.Homotopic.Quotient.refl b
  have hpath : pW.toPath.map (overlapInclusion U V).continuous = p.toPath := by ext t; rfl
  have h := (SimplyConnectedSpace.paths_homotopic
    (a.trans (pW.toPath.trans c.symm)) (Path.refl bW)).map (overlapInclusion U V)
  have hclass := Path.Homotopic.Quotient.eq.mpr h
  have hconst : (Path.refl bW).map (overlapInclusion U V).continuous = Path.refl b := by
    ext t
    rfl
  simp only [Path.map_trans, ← Path.map_symm, hpath, hconst] at hclass
  exact hclass



def cover : Bool → Set X
  | false => U
  | true => V



noncomputable def localValue (p : C(unitInterval, X)) : (FundamentalGroup U b)ᵐᵒᵖ := by
  classical
  exact if hp : ∀ t, p t ∈ U then
    Path.Homotopic.Quotient.basedContinuousTransport b (overlapTails U V hUV b hb)
      (p.restrictRange U hp)
  else 1



theorem localValue_first (p : C(unitInterval, X)) (hp : ∀ t, p t ∈ U) :
    localValue U V hUV b hb p =
      Path.Homotopic.Quotient.basedContinuousTransport b (overlapTails U V hUV b hb)
        (p.restrictRange U hp) := by
  simp only [localValue, dif_pos hp]



theorem localValue_second (p : C(unitInterval, X)) (hp : ∀ t, p t ∈ V) :
    localValue U V hUV b hb p = 1 := by
  classical
  by_cases hpU : ∀ t, p t ∈ U
  · rw [localValue_first U V hUV b hb p hpU]
    exact overlap_transport_eq_one U V hUV b hb _ hp
  · simp only [localValue, dif_neg hpU]

set_option backward.isDefEq.respectTransparency false in


noncomputable def localTransport : LocalPathTransport (cover U V) (FundamentalGroup U b)ᵐᵒᵖ where
  value := localValue U V hUV b hb
  map_const x := by
    classical
    by_cases hx : x ∈ U
    · rw [localValue_first U V hUV b hb _ (fun _ => hx)]
      exact Path.Homotopic.Quotient.basedContinuousTransport_const b _ ⟨x, hx⟩
    · simp [localValue, hx]
  square H i hH := by
    cases i with
    | false =>
      have hU : ∀ z, H z ∈ U := hH
      rw [localValue_first U V hUV b hb _ (fun t => hU (t, 0)),
        localValue_first U V hUV b hb _ (fun t => hU (1, t)),
        localValue_first U V hUV b hb _ (fun t => hU (0, t)),
        localValue_first U V hUV b hb _ (fun t => hU (t, 1))]
      exact Path.Homotopic.Quotient.basedContinuousTransport_square b
        (overlapTails U V hUV b hb) (H.restrictRange U hU)
    | true =>
      have hV : ∀ z, H z ∈ V := hH
      rw [localValue_second U V hUV b hb _ (fun t => hV (t, 0)),
        localValue_second U V hUV b hb _ (fun t => hV (1, t)),
        localValue_second U V hUV b hb _ (fun t => hV (0, t)),
        localValue_second U V hUV b hb _ (fun t => hV (t, 1))]

end VanKampen
