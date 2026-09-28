import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.Mathlib.InteriorContactFaces
import PoincareConjecture.Proofs.M76.Dehn.OriginalTwoBranchWindows

set_option autoImplicit false

open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn

local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

theorem exists_two_branch_chart_of_carrier_chart
    {X Y ι : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (charts : ι → OpenPartialHomeomorph Y V3) (p : X → Y) (w : TwoBranchWindow p)
    (A : Set X) (Q : OpenPartialHomeomorph Y V3) (c : V3 ≃L[ℝ] C3)
    (J K : Set V3) (region W : Set Y)
    (hQregion : Q.source ⊆ region) (hQw : Q.source ⊆ w.target)
    (hQPL : ∀ k, (charts k).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (hJ : J ⊆ Q.target)
    (hleft : ∀ y ∈ Q.source, y ∈ p '' (A ∩ w.left.source) ↔ (c (Q y)).2 = 0)
    (hK : (w.right.trans Q) '' (A ∩ (w.right.trans Q).source) ∩ J = K)
    {z : V3} (hzJ : z ∈ interior J)
    (T : OpenPartialHomeomorph V3 C3) (hzT : z ∈ T.source) (hTz : T z = 0)
    (hTs : T.source ⊆ interior J ∩ (Q.target ∩ Q.symm ⁻¹' W))
    (hTPL : LocallyPiecewiseAffineOn T T.source)
    (hTK : ∀ x ∈ T.source, x ∈ K ↔ (T x).1.1 = 0)
    (hheight : ∀ x ∈ T.source, (c x).2 = (T x).2) :
    ∃ B : OpenPartialHomeomorph Y V3,
      Q.symm z ∈ B.source ∧ B (Q.symm z) = 0 ∧
      B.source ⊆ W ∩ (Q.source ∩ region) ∧
      (∀ k, (charts k).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
      p ⁻¹' B.source = (w.left.source ∩ p ⁻¹' B.source) ∪
        (w.right.source ∩ p ⁻¹' B.source) ∧
      (∀ y ∈ B.source, y ∈ p '' (A ∩ w.left.source) ↔ (c (B y)).2 = 0) ∧
      ∀ y ∈ B.source, y ∈ p '' (A ∩ w.right.source) ↔ (c (B y)).1.1 = 0 := by
  let B := Q.trans (T.trans c.symm.toHomeomorph.toOpenPartialHomeomorph)
  have hzB : Q.symm z ∈ B.source := by
    refine ⟨Q.map_target (hJ (interior_subset hzJ)), ?_, mem_univ _⟩
    change Q (Q.symm z) ∈ T.source
    rwa [Q.right_inv (hJ (interior_subset hzJ))]
  have hvalue (y : Y) : c (B y) = T (Q y) := c.apply_symm_apply _
  have hsource (y : Y) (hy : y ∈ B.source) : y ∈ W ∩ (Q.source ∩ region) := by
    have hW : Q.symm (Q y) ∈ W := (hTs hy.2.1).2.2
    rw [Q.left_inv hy.1] at hW
    exact ⟨hW, hy.1, hQregion hy.1⟩
  refine ⟨B, hzB, ?_, hsource, ?_, ?_, ?_, ?_⟩
  · change c.symm (T (Q (Q.symm z))) = 0
    rw [Q.right_inv (hJ (interior_subset hzJ)), hTz, map_zero]
  · intro k
    apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
    have hf := (locallyPiecewiseAffineOn_affine
      c.symm.toContinuousLinearMap.toContinuousAffineMap isOpen_univ).comp hTPL
    exact (hf.comp (hQPL k).1).mono ((charts k).symm.trans B).open_source
      (fun x hx ↦ ⟨⟨hx.1, hx.2.1⟩, hx.2.2.1, mem_univ _⟩)
  · ext x
    constructor
    · intro hx
      rcases w.whole_preimage.subset (hQw (hsource _ hx).2.1) with hl | hr
      · exact Or.inl ⟨hl, hx⟩
      · exact Or.inr ⟨hr, hx⟩
    · exact fun h ↦ h.elim And.right And.right
  · intro y hy
    rw [hleft y hy.1, hvalue, hheight (Q y) hy.2.1]
  · intro y hy
    have hyJ : Q y ∈ J := interior_subset (hTs hy.2.1).1
    have hright : y ∈ p '' (A ∩ w.right.source) ↔ Q y ∈ K := by
      rw [← hK]
      constructor
      · rintro ⟨x, ⟨hxA, hxw⟩, hxy⟩
        refine ⟨⟨x, ⟨hxA, hxw, ?_⟩, ?_⟩, hyJ⟩
        · change w.right x ∈ Q.source
          rw [congrFun w.right_eq x, hxy]
          exact hy.1
        · change Q (w.right x) = Q y
          rw [congrFun w.right_eq x, hxy]
      · rintro ⟨⟨x, ⟨hxA, hxT⟩, hxy⟩, _⟩
        refine ⟨x, ⟨hxA, hxT.1⟩, ?_⟩
        have hxQ : w.right x ∈ Q.source := hxT.2
        rw [congrFun w.right_eq x] at hxQ
        apply Q.injOn hxQ hy.1
        change Q (w.right x) = Q y at hxy
        rwa [congrFun w.right_eq x] at hxy
    rw [hright, hvalue]
    exact hTK (Q y) hy.2.1

theorem exists_swapped_crossing_chart
    {Y ι : Type*} [TopologicalSpace Y]
    (charts : ι → OpenPartialHomeomorph Y V3) (c : V3 ≃L[ℝ] C3)
    (T : OpenPartialHomeomorph Y V3)
    (hTPL : ∀ k, (charts k).symm.trans T ∈ piecewiseAffineGroupoid V3) :
    ∃ B : OpenPartialHomeomorph Y V3,
      B.source = T.source ∧ (∀ y, T y = 0 → B y = 0) ∧
      (∀ k, (charts k).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
      (∀ y, (c (B y)).2 = (c (T y)).1.1) ∧
      ∀ y, (c (B y)).1.1 = (c (T y)).2 := by
  let swap : C3 ≃L[ℝ] C3 :=
    { toFun := fun z ↦ ((z.2, z.1.2), z.1.1)
      invFun := fun z ↦ ((z.2, z.1.2), z.1.1)
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let L := (c.trans swap).trans c.symm
  let B := T.trans L.toHomeomorph.toOpenPartialHomeomorph
  have hBs : B.source = T.source := by ext y; simp [B]
  refine ⟨B, hBs, ?_, ?_, ?_, ?_⟩
  · intro y hy
    change L (T y) = 0
    rw [hy, map_zero]
  · intro k
    apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
    have hcomp := (locallyPiecewiseAffineOn_affine
      L.toContinuousLinearMap.toContinuousAffineMap isOpen_univ).comp (hTPL k).1
    exact hcomp.mono ((charts k).symm.trans B).open_source
      (fun y hy ↦ ⟨⟨hy.1, hBs.subset hy.2⟩, mem_univ _⟩)
  · intro y
    change (c (c.symm (swap (c (T y))))).2 = _
    rw [c.apply_symm_apply]
    rfl
  · intro y
    change (c (c.symm (swap (c (T y))))).1.1 = _
    rw [c.apply_symm_apply]
    rfl

end PoincareConjecture.M76.Dehn
