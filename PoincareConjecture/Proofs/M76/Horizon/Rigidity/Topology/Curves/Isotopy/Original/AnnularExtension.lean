import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.OriginalAnnulusMark
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Support.ClosedExtension

set_option autoImplicit false
open Set Geometry PLAnnularStrip Topology

namespace PoincareConjecture.M76.Dehn

local notation "Ann" => squareAnnulus 8 1

variable {X T : Type*} [TopologicalSpace X] [TopologicalSpace T]
  {B S : Set X}

def originalAnnularChart (A : Ann ≃ₜ B) (hBS : B ⊆ S) :
    Ann ≃ₜ ((Subtype.val : S → X) ⁻¹' B) where
  toFun x := ⟨⟨A x, hBS (A x).property⟩, (A x).property⟩
  invFun y := A.symm ⟨y.1.1, y.2⟩
  left_inv x := A.symm_apply_apply x
  right_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : B => (z : X)) (A.apply_symm_apply ⟨y.1.1, y.2⟩)
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private theorem originalAnnularChart_depth_at_frontier
    (A : Ann ≃ₜ B) (hBS : B ⊆ S)
    (hmark : IsOpen ((Subtype.val : S → X) ⁻¹' originalAnnulusOpenMark A))
    (x : (Subtype.val : S → X) ⁻¹' B)
    (hx : (x : S) ∈ frontier ((Subtype.val : S → X) ⁻¹' B)) :
    depth 8 ((originalAnnularChart A hBS).symm x : ℝ × ℝ) = -1 ∨
      depth 8 ((originalAnnularChart A hBS).symm x : ℝ × ℝ) = 1 := by
  have hd := mem_squareAnnulus_iff_depth.mp
    ((originalAnnularChart A hBS).symm x).property
  have hn : ¬ (-1 < depth 8 ((originalAnnularChart A hBS).symm x : ℝ × ℝ) ∧
      depth 8 ((originalAnnularChart A hBS).symm x : ℝ × ℝ) < 1) := by
    intro hm
    have hm' : (x : S) ∈ (Subtype.val : S → X) ⁻¹' originalAnnulusOpenMark A :=
      (mem_originalAnnulusOpenMark_iff A ⟨x.1.1, x.2⟩).mpr hm
    have hi : (x : S) ∈ interior ((Subtype.val : S → X) ⁻¹' B) :=
      mem_interior_iff_mem_nhds.mpr
        (Filter.mem_of_superset (hmark.mem_nhds hm')
          (fun y hy => originalAnnulusOpenMark_subset A hy))
    exact hx.2 hi
  by_cases h : depth 8 ((originalAnnularChart A hBS).symm x : ℝ × ℝ) = -1
  · exact Or.inl h
  · exact Or.inr (le_antisymm hd.2 (not_lt.mp (fun hh => hn ⟨lt_of_le_of_ne hd.1 (Ne.symm h), hh⟩)))

private theorem originalAnnularConjugate_fixed_frontier
    (A : Ann ≃ₜ B) (hBS : B ⊆ S)
    (hmark : IsOpen ((Subtype.val : S → X) ⁻¹' originalAnnulusOpenMark A))
    (G : Ann ≃ₜ Ann)
    (hfix : ∀ x : Ann, depth 8 (x : ℝ × ℝ) = -1 ∨
      depth 8 (x : ℝ × ℝ) = 1 → G x = x)
    (x : (Subtype.val : S → X) ⁻¹' B)
    (hx : (x : S) ∈ frontier ((Subtype.val : S → X) ⁻¹' B)) :
    ((originalAnnularChart A hBS).symm.trans
      (G.trans (originalAnnularChart A hBS))) x = x := by
  change originalAnnularChart A hBS (G ((originalAnnularChart A hBS).symm x)) = x
  rw [hfix _ (originalAnnularChart_depth_at_frontier A hBS hmark x hx)]
  exact (originalAnnularChart A hBS).apply_symm_apply x

noncomputable def originalAnnularExtension
    (A : Ann ≃ₜ B) (hBS : B ⊆ S) (hB : IsClosed B)
    (hmark : IsOpen ((Subtype.val : S → X) ⁻¹' originalAnnulusOpenMark A))
    (G : Ann ≃ₜ Ann)
    (hfix : ∀ x : Ann, depth 8 (x : ℝ × ℝ) = -1 ∨
      depth 8 (x : ℝ × ℝ) = 1 → G x = x) : S ≃ₜ S :=
  ((originalAnnularChart A hBS).symm.trans
      (G.trans (originalAnnularChart A hBS))).closedExtension
    (hB.preimage continuous_subtype_val)
    (originalAnnularConjugate_fixed_frontier A hBS hmark G hfix)

theorem originalAnnularExtension_apply
    (A : Ann ≃ₜ B) (hBS : B ⊆ S) (hB : IsClosed B)
    (hmark : IsOpen ((Subtype.val : S → X) ⁻¹' originalAnnulusOpenMark A))
    (G : Ann ≃ₜ Ann)
    (hfix : ∀ x : Ann, depth 8 (x : ℝ × ℝ) = -1 ∨
      depth 8 (x : ℝ × ℝ) = 1 → G x = x) (x : Ann) :
    originalAnnularExtension A hBS hB hmark G hfix ⟨A x, hBS (A x).property⟩ =
      ⟨A (G x), hBS (A (G x)).property⟩ := by
  unfold originalAnnularExtension
  rw [Homeomorph.closedExtension_apply_mem (x := (⟨A x, hBS (A x).property⟩ : S))
    _ _ _ (show (⟨A x, hBS (A x).property⟩ : S) ∈
      (Subtype.val : S → X) ⁻¹' B from (A x).property)]
  apply Subtype.ext
  change (A (G (A.symm (A x))) : X) = (A (G x) : X)
  rw [A.symm_apply_apply]

theorem continuous_originalAnnularExtension
    (A : Ann ≃ₜ B) (hBS : B ⊆ S) (hB : IsClosed B)
    (hmark : IsOpen ((Subtype.val : S → X) ⁻¹' originalAnnulusOpenMark A))
    (G : T → Ann ≃ₜ Ann) (hc : Continuous (fun z : T × Ann => G z.1 z.2))
    (hfix : ∀ t (x : Ann), depth 8 (x : ℝ × ℝ) = -1 ∨
      depth 8 (x : ℝ × ℝ) = 1 → G t x = x) :
    Continuous (fun z : T × S =>
      originalAnnularExtension A hBS hB hmark (G z.1) (hfix z.1) z.2) := by
  let C := originalAnnularChart A hBS
  have h : Continuous (fun z : T × ((Subtype.val : S → X) ⁻¹' B) =>
      (C.symm.trans ((G z.1).trans C)) z.2) :=
    C.continuous.comp (hc.comp
      (continuous_fst.prodMk (C.symm.continuous.comp continuous_snd)))
  exact Homeomorph.continuous_closedExtension_family
    (fun t => C.symm.trans ((G t).trans C))
    (hB.preimage continuous_subtype_val) h
    (fun t => originalAnnularConjugate_fixed_frontier A hBS hmark (G t) (hfix t))

theorem continuous_originalAnnularExtension_symm
    (A : Ann ≃ₜ B) (hBS : B ⊆ S) (hB : IsClosed B)
    (hmark : IsOpen ((Subtype.val : S → X) ⁻¹' originalAnnulusOpenMark A))
    (G : T → Ann ≃ₜ Ann) (hc : Continuous (fun z : T × Ann => (G z.1).symm z.2))
    (hfix : ∀ t (x : Ann), depth 8 (x : ℝ × ℝ) = -1 ∨
      depth 8 (x : ℝ × ℝ) = 1 → G t x = x) :
    Continuous (fun z : T × S =>
      (originalAnnularExtension A hBS hB hmark (G z.1) (hfix z.1)).symm z.2) := by
  let C := originalAnnularChart A hBS
  have h : Continuous (fun z : T × ((Subtype.val : S → X) ⁻¹' B) =>
      (C.symm.trans ((G z.1).trans C)).symm z.2) :=
    C.continuous.comp (hc.comp
      (continuous_fst.prodMk (C.symm.continuous.comp continuous_snd)))
  exact Homeomorph.continuous_closedExtension_family_symm
    (fun t => C.symm.trans ((G t).trans C))
    (hB.preimage continuous_subtype_val) h
    (fun t => originalAnnularConjugate_fixed_frontier A hBS hmark (G t) (hfix t))

theorem originalAnnularExtension_fixed_off_mark
    (A : Ann ≃ₜ B) (hBS : B ⊆ S) (hB : IsClosed B)
    (hmark : IsOpen ((Subtype.val : S → X) ⁻¹' originalAnnulusOpenMark A))
    (G : Ann ≃ₜ Ann)
    (hfix : ∀ x : Ann, depth 8 (x : ℝ × ℝ) = -1 ∨
      depth 8 (x : ℝ × ℝ) = 1 → G x = x)
    (x : S) (hx : (x : X) ∉ originalAnnulusOpenMark A) :
    originalAnnularExtension A hBS hB hmark G hfix x = x := by
  by_cases hxB : (x : X) ∈ B
  · let z : Ann := A.symm ⟨x, hxB⟩
    have hval : (⟨A z, hBS (A z).property⟩ : S) = x := by
      apply Subtype.ext
      exact congrArg (fun y : B => (y : X)) (A.apply_symm_apply ⟨x, hxB⟩)
    have hd := mem_squareAnnulus_iff_depth.mp z.property
    have hn : ¬ (-1 < depth 8 (z : ℝ × ℝ) ∧ depth 8 (z : ℝ × ℝ) < 1) :=
      fun hz => hx ((mem_originalAnnulusOpenMark_iff A ⟨x, hxB⟩).mpr hz)
    have hends : depth 8 (z : ℝ × ℝ) = -1 ∨ depth 8 (z : ℝ × ℝ) = 1 := by
      by_cases h : depth 8 (z : ℝ × ℝ) = -1
      · exact Or.inl h
      · exact Or.inr (le_antisymm hd.2
          (not_lt.mp (fun hh => hn ⟨lt_of_le_of_ne hd.1 (Ne.symm h), hh⟩)))
    conv_lhs => rw [← hval]
    rw [originalAnnularExtension_apply, hfix z hends]
    exact hval
  · exact Homeomorph.closedExtension_apply_notMem _ _ _
      (show x ∉ (Subtype.val : S → X) ⁻¹' B from hxB)

theorem originalAnnularExtension_eq_refl
    (A : Ann ≃ₜ B) (hBS : B ⊆ S) (hB : IsClosed B)
    (hmark : IsOpen ((Subtype.val : S → X) ⁻¹' originalAnnulusOpenMark A))
    (G : Ann ≃ₜ Ann)
    (hfix : ∀ x : Ann, depth 8 (x : ℝ × ℝ) = -1 ∨
      depth 8 (x : ℝ × ℝ) = 1 → G x = x) (hG : ∀ x, G x = x) :
    originalAnnularExtension A hBS hB hmark G hfix = Homeomorph.refl S := by
  apply Homeomorph.ext
  intro x
  by_cases hxB : (x : X) ∈ B
  · let z : Ann := A.symm ⟨x, hxB⟩
    have hval : (⟨A z, hBS (A z).property⟩ : S) = x := by
      apply Subtype.ext
      exact congrArg (fun y : B => (y : X)) (A.apply_symm_apply ⟨x, hxB⟩)
    change originalAnnularExtension A hBS hB hmark G hfix x = x
    conv_lhs => rw [← hval]
    rw [originalAnnularExtension_apply, hG z]
    exact hval
  · exact originalAnnularExtension_fixed_off_mark A hBS hB hmark G hfix x
      (fun hx => hxB (originalAnnulusOpenMark_subset A hx))

theorem originalAnnularExtension_symm
    (A : Ann ≃ₜ B) (hBS : B ⊆ S) (hB : IsClosed B)
    (hmark : IsOpen ((Subtype.val : S → X) ⁻¹' originalAnnulusOpenMark A))
    (G : Ann ≃ₜ Ann)
    (hfix : ∀ x : Ann, depth 8 (x : ℝ × ℝ) = -1 ∨
      depth 8 (x : ℝ × ℝ) = 1 → G x = x)
    (hfixInv : ∀ x : Ann, depth 8 (x : ℝ × ℝ) = -1 ∨
      depth 8 (x : ℝ × ℝ) = 1 → G.symm x = x) :
    (originalAnnularExtension A hBS hB hmark G hfix).symm =
      originalAnnularExtension A hBS hB hmark G.symm hfixInv := by
  apply Homeomorph.ext
  intro x
  rfl

open unitInterval in

noncomputable def originalAnnularHomotopyRel
    (A : Ann ≃ₜ B) (hBS : B ⊆ S) (hB : IsClosed B)
    (hmark : IsOpen ((Subtype.val : S → X) ⁻¹' originalAnnulusOpenMark A))
    (G : I → Ann ≃ₜ Ann) (hc : Continuous (fun z : I × Ann => G z.1 z.2))
    (hfix : ∀ t (x : Ann), depth 8 (x : ℝ × ℝ) = -1 ∨
      depth 8 (x : ℝ × ℝ) = 1 → G t x = x)
    (hzero : ∀ x, G 0 x = x) :
    (ContinuousMap.id S).HomotopyRel
      ⟨originalAnnularExtension A hBS hB hmark (G 1) (hfix 1),
        (originalAnnularExtension A hBS hB hmark (G 1) (hfix 1)).continuous⟩
      ((Subtype.val : S → X) ⁻¹' originalAnnulusOpenMark A)ᶜ where
  toFun z := originalAnnularExtension A hBS hB hmark (G z.1) (hfix z.1) z.2
  continuous_toFun := continuous_originalAnnularExtension A hBS hB hmark G hc hfix
  map_zero_left x := by
    rw [originalAnnularExtension_eq_refl A hBS hB hmark (G 0) (hfix 0) hzero]
    rfl
  map_one_left _ := rfl
  prop' t x hx := originalAnnularExtension_fixed_off_mark A hBS hB hmark (G t) (hfix t) x hx

end PoincareConjecture.M76.Dehn
