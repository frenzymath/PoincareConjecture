import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.LevelSets

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1

private def interHomeomorphNested {X : Type*} [TopologicalSpace X] (L U : Set X) :
    (L ∩ U : Set X) ≃ₜ ((Subtype.val : L → X) ⁻¹' U) where
  toFun x := ⟨⟨x.val, x.property.1⟩, x.property.2⟩
  invFun x := ⟨x.val.val, x.val.property, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

private def componentEquivOfHomeomorph {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (H : X ≃ₜ Y) : ConnectedComponents X ≃ ConnectedComponents Y :=
  (H.isQuotientMap.isCoinducing.connectedComponentsHomeomorph fun y => by
    have hfiber : H ⁻¹' {y} = {H.symm y} := by
      ext x
      exact H.toEquiv.eq_symm_apply.symm
    rw [hfiber]
    exact isConnected_singleton).toEquiv

theorem exists_level_homeomorph_retained_of_disk_splicing
    (f f' : S2 → E3) (v : E3) (c : Real)
    (e d : OpenPartialHomeomorph E2 S2)
    (hesource : closedBall 0 1 ⊆ e.source)
    (hdclosed : d '' closedBall 0 1 = (e '' ball 0 1)ᶜ)
    (g : E2 → E3)
    (hcap : ∀ x ∈ closedBall 0 1, f' (d x) = g x)
    (hoff : ∀ p ∈ e '' closedBall 0 1, f' p = f p)
    (havoid : ∀ x ∈ closedBall 0 1, inner Real v (g x) ≠ c) :
    let L := (fun p => inner Real v (f p)) ⁻¹' {c}
    let L' := (fun p => inner Real v (f' p)) ⁻¹' {c}
    ∃ H : L' ≃ₜ ((Subtype.val : L → S2) ⁻¹' (e '' ball 0 1)),
      ∀ x : L', (H x).val.val = x.val := by
  obtain ⟨hlevel, _⟩ := level_eq_and_eventuallyEq_of_disk_splicing
    f f' v c e d hesource hdclosed g hcap hoff havoid
  exact ⟨(Homeomorph.setCongr hlevel).trans (interHomeomorphNested _ _), fun _ => rfl⟩

theorem card_level_components_of_parallel_disk_splicing
    (f fMinus fPlus : S2 → E3) (v : E3) {c ε a : Real}
    (ha : 0 < a) (haε : a < ε)
    (T : OpenPartialHomeomorph (S1 × Real) S2)
    (hsource : T.source = univ ×ˢ Ioo (-ε) ε)
    (hheight : ∀ q t, t ∈ Ioo (-ε) ε → inner Real v (f (T (q, t))) = c + t)
    (p : S2) (hp : inner Real v (f p) = c)
    (hcenter : range (fun q : S1 => T (q, 0)) =
      connectedComponentIn ((fun p => inner Real v (f p)) ⁻¹' {c}) p)
    (eMinus ePlus dMinus dPlus : OpenPartialHomeomorph E2 S2)
    (hsMinus : closedBall 0 1 ⊆ eMinus.source)
    (hsPlus : closedBall 0 1 ⊆ ePlus.source)
    (hdisjoint : Disjoint (eMinus '' closedBall 0 1) (ePlus '' closedBall 0 1))
    (hslab : T '' (univ ×ˢ Icc (-a) a) =
      (eMinus '' ball 0 1 ∪ ePlus '' ball 0 1)ᶜ)
    (hdMinus : dMinus '' closedBall 0 1 = (eMinus '' ball 0 1)ᶜ)
    (hdPlus : dPlus '' closedBall 0 1 = (ePlus '' ball 0 1)ᶜ)
    (gMinus gPlus : E2 → E3)
    (hcapMinus : ∀ x ∈ closedBall 0 1, fMinus (dMinus x) = gMinus x)
    (hcapPlus : ∀ x ∈ closedBall 0 1, fPlus (dPlus x) = gPlus x)
    (hoffMinus : ∀ p ∈ eMinus '' closedBall 0 1, fMinus p = f p)
    (hoffPlus : ∀ p ∈ ePlus '' closedBall 0 1, fPlus p = f p)
    (havoidMinus : ∀ x ∈ closedBall 0 1, inner Real v (gMinus x) ≠ c)
    (havoidPlus : ∀ x ∈ closedBall 0 1, inner Real v (gPlus x) ≠ c)
    [Finite (ConnectedComponents ((fun p => inner Real v (f p)) ⁻¹' {c}))] :
    let L := (fun p => inner Real v (f p)) ⁻¹' {c}
    let Lminus := (fun p => inner Real v (fMinus p)) ⁻¹' {c}
    let Lplus := (fun p => inner Real v (fPlus p)) ⁻¹' {c}
    Finite (ConnectedComponents Lminus) ∧ Finite (ConnectedComponents Lplus) ∧
      Nat.card (ConnectedComponents Lminus) + Nat.card (ConnectedComponents Lplus) + 1 =
        Nat.card (ConnectedComponents L) ∧
      Nat.card (ConnectedComponents Lminus) + Nat.card (ConnectedComponents Lplus) <
        Nat.card (ConnectedComponents L) := by
  let L := (fun p => inner Real v (f p)) ⁻¹' {c}
  let U : Set L := Subtype.val ⁻¹' (eMinus '' ball 0 1)
  let V : Set L := Subtype.val ⁻¹' (ePlus '' ball 0 1)
  let Lminus := (fun p => inner Real v (fMinus p)) ⁻¹' {c}
  let Lplus := (fun p => inner Real v (fPlus p)) ⁻¹' {c}
  obtain ⟨hU, hV, hcard, hlt⟩ := card_level_components_of_parallel_disks
    ha haε T hsource hheight p hp hcenter eMinus ePlus hsMinus hsPlus hdisjoint hslab
  let : Finite (ConnectedComponents U) := hU
  let : Finite (ConnectedComponents V) := hV
  obtain ⟨Hminus, _⟩ := exists_level_homeomorph_retained_of_disk_splicing
    f fMinus v c eMinus dMinus hsMinus hdMinus gMinus hcapMinus hoffMinus havoidMinus
  obtain ⟨Hplus, _⟩ := exists_level_homeomorph_retained_of_disk_splicing
    f fPlus v c ePlus dPlus hsPlus hdPlus gPlus hcapPlus hoffPlus havoidPlus
  let Eminus : ConnectedComponents Lminus ≃ ConnectedComponents U :=
    componentEquivOfHomeomorph Hminus
  let Eplus : ConnectedComponents Lplus ≃ ConnectedComponents V :=
    componentEquivOfHomeomorph Hplus
  let : Finite (ConnectedComponents Lminus) := Finite.of_equiv _ Eminus.symm
  let : Finite (ConnectedComponents Lplus) := Finite.of_equiv _ Eplus.symm
  refine ⟨inferInstance, inferInstance, ?_, ?_⟩
  · exact (congrArg₂ (fun m n : Nat => m + n + 1)
      (Nat.card_congr Eminus) (Nat.card_congr Eplus)).trans hcard
  · rw [Nat.card_congr Eminus, Nat.card_congr Eplus]
    exact hlt

end Poincare.Manifold.Schoenflies
