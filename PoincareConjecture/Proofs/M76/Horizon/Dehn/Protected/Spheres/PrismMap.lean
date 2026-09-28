import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProtectedGeometricInputs
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CubePrismBoundary










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "E" => (V2 × ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

namespace HamiltonProtectedDehnDisks

noncomputable section

def capHeight (b : Bool) : ℝ := if b then 3 / 2 else -(3 / 2)

def prismCap (b : Bool) : Set E := D ×ˢ {capHeight b}

def prismSide : Set E := Q ×ˢ Icc (-(3 / 2 : ℝ)) (3 / 2)

def prismLift : E →L[ℝ] (V2 × V1) :=
  (ContinuousLinearMap.fst ℝ V2 ℝ).prod
    (ContinuousLinearMap.pi fun _ : Fin 1 ↦ ContinuousLinearMap.snd ℝ V2 ℝ)

theorem prismLift_mem_block {x : E} (hx : x ∈ D ×ˢ Icc (-(3 / 2 : ℝ)) (3 / 2)) :
    prismLift x ∈ D ×ˢ closedBall (0 : V1) 2 := by
  refine ⟨hx.1, ?_⟩
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  intro i
  change ‖x.2‖ ≤ 2
  rw [Real.norm_eq_abs]
  exact (abs_le.mpr hx.2).trans (by norm_num)

theorem prism_boundary_eq :
    cubePrismBoundary (-(3 / 2 : ℝ)) (3 / 2) =
      (prismCap false ∪ prismCap true) ∪ prismSide := by
  ext x
  simp only [cubePrismBoundary, prismCap, prismSide, capHeight, Bool.false_eq_true,
    if_false, if_true, mem_union, mem_prod, mem_insert_iff, mem_singleton_iff]
  tauto

variable {L : Submodule ℤ V1} {α : Type*}
  {e : α → OpenPartialHomeomorph (LatticeHandleAmbient (Fin 2) (Fin 1) L) V3}
  (T : HamiltonProtectedDehnDisks L e)

noncomputable def prismMap (x : E) : LatticeHandleAmbient (Fin 2) (Fin 1) L :=
  if x.2 = capHeight false then T.map false x.1
  else if x.2 = capHeight true then T.map true x.1
  else hamiltonMarkedProjection (Fin 2) (Fin 1) L (prismLift x)

theorem prismMap_cap (b : Bool) {x : E} (hx : x ∈ prismCap b) :
    T.prismMap x = T.map b x.1 := by
  have ht : x.2 = capHeight b := hx.2
  cases b <;> norm_num [prismMap, ht, capHeight]

theorem prismMap_side {x : E} (hx : x ∈ prismSide) :
    T.prismMap x = hamiltonMarkedProjection (Fin 2) (Fin 1) L (prismLift x) := by
  dsimp only [prismMap]
  split_ifs with hneg hpos
  · rw [T.boundary_values false x.1 hx.1]
    congr 1
    exact congrArg QuotientAddGroup.mk (funext fun _ ↦ hneg.symm)
  · rw [T.boundary_values true x.1 hx.1]
    congr 1
    exact congrArg QuotientAddGroup.mk (funext fun _ ↦ hpos.symm)
  · rfl

theorem prismMap_cap_mem (b : Bool) {x : E} (hx : x ∈ prismCap b) :
    T.prismMap x ∈ T.surface b := by
  rw [T.prismMap_cap b hx, T.map_eq b ⟨x.1, hx.1⟩]
  exact (T.parametrization b ⟨x.1, hx.1⟩).property

theorem prismMap_side_old_boundary {x : E} (hx : x ∈ prismSide) :
    T.prismMap x ∈ frontier (latticeHandleDomain (Fin 2) (Fin 1) L) := by
  rw [T.prismMap_side hx, latticeHandleDomain, frontier_prod_univ_eq,
    frontier_closedBall _ one_ne_zero]
  exact ⟨hx.1, mem_univ _⟩


theorem prismMap_injOn {h : OpenPartialHomeomorph (V2 × V1) V3}
    (retained : HamiltonRetainedBlockChart (Fin 2) (Fin 1) L e h) :
    InjOn T.prismMap (cubePrismBoundary (-(3 / 2 : ℝ)) (3 / 2)) := by
  have hlift : Function.Injective prismLift := by
    intro x y hxy
    exact Prod.ext (congrArg (fun z : V2 × V1 ↦ z.1) hxy)
      (congrArg (fun z : V2 × V1 ↦ z.2 0) hxy)
  have hcap (b : Bool) : InjOn T.prismMap (prismCap b) := by
    intro x hx y hy hxy
    rw [T.prismMap_cap b hx, T.prismMap_cap b hy,
      T.map_eq b ⟨x.1, hx.1⟩, T.map_eq b ⟨y.1, hy.1⟩] at hxy
    exact Prod.ext (congrArg Subtype.val ((T.parametrization b).injective
      (Subtype.ext hxy))) (hx.2.trans hy.2.symm)
  have hside : InjOn T.prismMap prismSide := by
    intro x hx y hy hxy
    rw [T.prismMap_side hx, T.prismMap_side hy] at hxy
    exact hlift (retained.quotient_injective
      (prismLift_mem_block ⟨sphere_subset_closedBall hx.1, hx.2⟩)
      (prismLift_mem_block ⟨sphere_subset_closedBall hy.1, hy.2⟩) hxy)
  have hcross (b : Bool) {x y : E} (hx : x ∈ prismCap b) (hy : y ∈ prismSide)
      (hxy : T.prismMap x = T.prismMap y) : x = y := by
    have hxb : (T.parametrization b ⟨x.1, hx.1⟩ :
        LatticeHandleAmbient (Fin 2) (Fin 1) L) ∈
          frontier (latticeHandleDomain (Fin 2) (Fin 1) L) := by
      rw [← T.map_eq, ← T.prismMap_cap b hx, hxy]
      exact T.prismMap_side_old_boundary hy
    have hxq := (T.old_boundary_iff b ⟨x.1, hx.1⟩).mp hxb
    have hxs : x ∈ prismSide := by
      refine ⟨hxq, ?_⟩
      have ht : x.2 = capHeight b := hx.2
      rw [ht]
      cases b <;> norm_num [capHeight]
    exact hside hxs hy hxy
  have hsep {x y : E} (hx : x ∈ prismCap false) (hy : y ∈ prismCap true)
      (hxy : T.prismMap x = T.prismMap y) : False :=
    Set.disjoint_left.mp T.disjoint (T.prismMap_cap_mem false hx)
      (hxy.symm ▸ T.prismMap_cap_mem true hy)
  rw [prism_boundary_eq]
  intro x hx y hy hxy
  rcases hx with (hx | hx) | hx <;> rcases hy with (hy | hy) | hy
  · exact hcap false hx hy hxy
  · exact (hsep hx hy hxy).elim
  · exact hcross false hx hy hxy
  · exact (hsep hy hx hxy.symm).elim
  · exact hcap true hx hy hxy
  · exact hcross true hx hy hxy
  · exact (hcross false hy hx hxy.symm).symm
  · exact (hcross true hy hx hxy.symm).symm
  · exact hside hx hy hxy



theorem prismMap_image :
    T.prismMap '' cubePrismBoundary (-(3 / 2 : ℝ)) (3 / 2) =
      (⋃ b, T.surface b) ∪ hamiltonAttachingBlock (Fin 2) (Fin 1) L (3 / 2) := by
  have hcap (b : Bool) : T.prismMap '' prismCap b = T.surface b := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact T.prismMap_cap_mem b hx
    · intro y hy
      let x := (T.parametrization b).symm ⟨y, hy⟩
      refine ⟨(x, capHeight b), ⟨x.property, rfl⟩, ?_⟩
      rw [T.prismMap_cap b (x := (x, capHeight b)) ⟨x.property, rfl⟩, T.map_eq b x]
      exact congrArg Subtype.val ((T.parametrization b).apply_symm_apply ⟨y, hy⟩)
  have hside : T.prismMap '' prismSide =
      hamiltonAttachingBlock (Fin 2) (Fin 1) L (3 / 2) := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      rw [T.prismMap_side hx]
      refine ⟨prismLift x, ⟨hx.1, ?_⟩, rfl⟩
      rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 3/2)]
      intro i
      exact abs_le.mpr hx.2
    · rintro _ ⟨z, hz, rfl⟩
      have ht : z.2 0 ∈ Icc (-(3/2:ℝ)) (3/2) := by
        exact abs_le.mp ((norm_le_pi_norm z.2 0).trans (mem_closedBall_zero_iff.mp hz.2))
      refine ⟨(z.1, z.2 0), ⟨hz.1, ht⟩, ?_⟩
      rw [T.prismMap_side ⟨hz.1, ht⟩]
      congr 1
      apply Prod.ext
      · rfl
      · funext i
        exact congrArg z.2 (Subsingleton.elim 0 i)
  rw [prism_boundary_eq, image_union, image_union, hcap, hcap, hside]
  ext x
  simp only [mem_union, mem_iUnion, Bool.exists_bool]

end

end HamiltonProtectedDehnDisks

end PoincareConjecture.M76
