import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.TerminalBoundaryArcCoordinates
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.TwoProperArcCuts
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionIncidence


set_option autoImplicit false
open Set
namespace PoincareConjecture.M76
local notation "J" => Icc (-1 : ℝ) 1

theorem closed_cylinder_end_cover
    {X Y Z : Type*} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace Y] [CompactSpace Y] [TopologicalSpace Z] [T2Space Z]
    {A T F : Set X} (hA : IsClosed A) (W : (Y × J) ≃ₜ T)
    (hcover : A ∪ T = F)
    (hends : ∀ z, (W z : X) ∈ A ↔ (z.2 : ℝ) = -1 ∨ (z.2 : ℝ) = 1)
    (p : C(X,Z)) (a : Bool → Z) (hai : Function.Injective a)
    (hpa : ∀ x ∈ A, p x = a false ∨ p x = a true)
    (hlabel : ∀ side y,
      p (W (y,⟨if side then 1 else -1,by cases side <;> norm_num⟩)) = a side) :
    let B := fun side : Bool => (fun z => (W z : X)) ''
      {z : Y × J | if side then 0 ≤ (z.2 : ℝ) else (z.2 : ℝ) ≤ 0}
    let End := fun side : Bool => (A ∩ p ⁻¹' {a side}) ∪ B side
    (∀ side, IsClosed (End side)) ∧ End false ∪ End true = F ∧
      End false ∩ End true = (fun z => (W z : X)) '' {z | (z.2 : ℝ) = 0} := by
  classical
  intro B End
  have hBclosed (side : Bool) : IsClosed (B side) := by
    apply IsCompact.isClosed
    apply IsCompact.image _ (continuous_subtype_val.comp W.continuous)
    apply IsClosed.isCompact
    cases side <;> simp only [Bool.false_eq_true,ite_false,ite_true]
    · exact isClosed_le (continuous_subtype_val.comp continuous_snd) continuous_const
    · exact isClosed_le continuous_const (continuous_subtype_val.comp continuous_snd)
  have hEndclosed (side : Bool) : IsClosed (End side) :=
    (hA.inter (isClosed_singleton.preimage p.continuous)).union (hBclosed side)
  have hBT (side : Bool) : B side ⊆ T := fun x hx => by
    obtain ⟨z,_,rfl⟩ := hx
    exact (W z).property
  have hBcover : B false ∪ B true = T := by
    apply Subset.antisymm (union_subset (hBT false) (hBT true))
    intro x hx
    obtain ⟨z,hz⟩ := W.surjective ⟨x,hx⟩
    by_cases h : (z.2 : ℝ) ≤ 0
    · exact Or.inl ⟨z,h,congrArg Subtype.val hz⟩
    · exact Or.inr ⟨z,(lt_of_not_ge h).le,congrArg Subtype.val hz⟩
  have hEcover : End false ∪ End true = F := by
    rw [←hcover]
    apply Subset.antisymm
    · rintro x ((hx|hx)|(hx|hx))
      · exact Or.inl hx.1
      · exact Or.inr (hBT false hx)
      · exact Or.inl hx.1
      · exact Or.inr (hBT true hx)
    · rintro x (hx|hx)
      · rcases hpa x hx with h|h
        · exact Or.inl (Or.inl ⟨hx,h⟩)
        · exact Or.inr (Or.inl ⟨hx,h⟩)
      · rcases hBcover.symm.subset hx with h|h
        · exact Or.inl (Or.inr h)
        · exact Or.inr (Or.inr h)
  have hne : a false ≠ a true := fun h => Bool.false_ne_true (hai h)
  have hcross0 : Disjoint (A ∩ p ⁻¹' {a false}) (B true) := by
    apply disjoint_left.mpr
    rintro x ⟨hxA,hxp⟩ ⟨z,hz,rfl⟩
    rcases (hends z).mp hxA with hm|hp
    · change 0 ≤ (z.2 : ℝ) at hz
      linarith
    · have heq : z = (z.1,⟨1,by norm_num⟩) := Prod.ext rfl (Subtype.ext hp)
      have hh : p (W z) = a true := by rw [heq]; exact hlabel true z.1
      apply hne
      exact hxp.symm.trans hh
  have hcross1 : Disjoint (B false) (A ∩ p ⁻¹' {a true}) := by
    apply disjoint_left.mpr
    rintro x ⟨z,hz,rfl⟩ ⟨hxA,hxp⟩
    rcases (hends z).mp hxA with hm|hp
    · have heq : z = (z.1,⟨-1,by norm_num⟩) := Prod.ext rfl (Subtype.ext hm)
      have hh : p (W z) = a false := by rw [heq]; exact hlabel false z.1
      apply hne
      exact hh.symm.trans hxp
    · change (z.2 : ℝ) ≤ 0 at hz
      linarith
  refine ⟨hEndclosed,hEcover,?_⟩
  apply Subset.antisymm
  · rintro x ⟨hx|hx,hy|hy⟩
    · exact (hne (hx.2.symm.trans hy.2)).elim
    · exact (disjoint_left.mp hcross0 hx hy).elim
    · exact (disjoint_left.mp hcross1 hx hy).elim
    · obtain ⟨z,hz,hzx⟩ := hx
      obtain ⟨w,hw,hwx⟩ := hy
      have hzw := W.injective (Subtype.ext (hzx.trans hwx.symm))
      change (z.2 : ℝ) ≤ 0 at hz
      change 0 ≤ (w.2 : ℝ) at hw
      refine ⟨z,?_,hzx⟩
      change (z.2 : ℝ) = 0
      rw [←hzw] at hw
      linarith
  · rintro x ⟨z,hz,rfl⟩
    exact ⟨Or.inr ⟨z,show (z.2 : ℝ) ≤ 0 by rw [hz],rfl⟩,
      Or.inr ⟨z,show 0 ≤ (z.2 : ℝ) by rw [hz],rfl⟩⟩

theorem original_arc_image_subset_one_closed_end
    {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA : IsClosed A) (hB : IsClosed B) (hcommon : A ∩ B = C)
    {U q : Set (ℝ × ℝ)} (hU : IsFinitePLBallPair ℝ U q)
    {f : (ℝ × ℝ) → X} (hf : ContinuousOn f U)
    (hcover : MapsTo f U (A ∪ B)) (hfree : Disjoint (f '' (U \ q)) C) :
    f '' U ⊆ A ∨ f '' U ⊆ B := by
  have hconn := hU.isConnected_sdiff.isPreconnected.image f (hf.mono sdiff_subset)
  have hsub : f '' (U \ q) ⊆ A ∪ B := by
    rintro _ ⟨x,hx,rfl⟩
    exact hcover hx.1
  have extend {T : Set X} (hT : IsClosed T) (hFT : f '' (U \ q) ⊆ T) : f '' U ⊆ T := by
    rintro _ ⟨x,hx,rfl⟩
    have hxcl : x ∈ closure (U \ q) := hU.closure_sdiff.symm ▸ hx
    have hh := ((hf x hx).mono sdiff_subset).mem_closure hxcl
      (fun y hy => hFT (mem_image_of_mem f hy))
    exact hT.closure_eq ▸ hh
  rcases Dehn.isPreconnected_subset_one_cut_piece hconn hA hB hsub hcommon hfree with h|h
  · exact Or.inl (extend hA h)
  · exact Or.inr (extend hB h)

end PoincareConjecture.M76
