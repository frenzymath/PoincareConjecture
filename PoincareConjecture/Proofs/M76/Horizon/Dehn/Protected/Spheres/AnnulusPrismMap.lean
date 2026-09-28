import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProtectedGeometricInputs
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CubePrismBoundary

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonProtectedDehnAnnulus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "E" => (V2 × ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

noncomputable section

def capHeight (b : Bool) : ℝ := if b then 1 else -1

def prismCap (b : Bool) : Set E := D ×ˢ {capHeight b}

def prismSide : Set E := Q ×ˢ Icc (-1 : ℝ) 1

def sideLift : E →L[ℝ] (V1 × V2) :=
  (ContinuousLinearMap.pi fun _ : Fin 1 ↦ ContinuousLinearMap.snd ℝ V2 ℝ).prod
    (ContinuousLinearMap.fst ℝ V2 ℝ)

def capLift : E →L[ℝ] (V1 × V2) :=
  (ContinuousLinearMap.pi fun _ : Fin 1 ↦ ContinuousLinearMap.snd ℝ V2 ℝ).prod
    ((3 / 2 : ℝ) • ContinuousLinearMap.fst ℝ V2 ℝ)

theorem sideLift_mem {x : E} (hx : x ∈ prismSide) :
    sideLift x ∈ closedBall (0 : V1) 1 ×ˢ Q := by
  refine ⟨?_, hx.1⟩
  rw [mem_closedBall_zero_iff]
  change ‖(fun _ : Fin 1 ↦ x.2)‖ ≤ 1
  rw [pi_norm_const, Real.norm_eq_abs]
  exact abs_le.mpr hx.2

theorem capLift_mem_block {x : E} (hx : x ∈ D ×ˢ Icc (-1 : ℝ) 1) :
    capLift x ∈ closedBall (0 : V1) 1 ×ˢ closedBall (0 : V2) 2 := by
  constructor
  · rw [mem_closedBall_zero_iff]
    change ‖(fun _ : Fin 1 ↦ x.2)‖ ≤ 1
    rw [pi_norm_const, Real.norm_eq_abs]
    exact abs_le.mpr hx.2
  · rw [mem_closedBall_zero_iff]
    change ‖(3 / 2 : ℝ) • x.1‖ ≤ 2
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
    have hn := mem_closedBall_zero_iff.mp hx.1
    linarith

theorem capHeight_mem (b : Bool) : capHeight b ∈ Icc (-1 : ℝ) 1 := by
  cases b <;> norm_num [capHeight]

theorem capLift_old_boundary (b : Bool) {x : E} (hx : x ∈ prismCap b) :
    (capLift x).1 ∈ sphere (0 : V1) 1 := by
  rw [mem_sphere_zero_iff_norm]
  change ‖(fun _ : Fin 1 ↦ x.2)‖ = 1
  rw [pi_norm_const, show x.2 = capHeight b from hx.2]
  cases b <;> norm_num [capHeight]

theorem prism_boundary_eq :
    cubePrismBoundary (-1 : ℝ) 1 = (prismCap false ∪ prismCap true) ∪ prismSide := by
  ext x
  simp only [cubePrismBoundary, prismCap, prismSide, capHeight, Bool.false_eq_true,
    if_false, if_true, mem_union, mem_prod, mem_insert_iff, mem_singleton_iff]
  tauto

variable {L : Submodule ℤ V2} {α : Type*}
  {e : α → OpenPartialHomeomorph (LatticeHandleAmbient (Fin 1) (Fin 2) L) V3}
  (T : HamiltonProtectedDehnAnnulus L e)

def prismMap (x : E) : LatticeHandleAmbient (Fin 1) (Fin 2) L :=
  if x.2 = -1 ∨ x.2 = 1 then hamiltonMarkedProjection (Fin 1) (Fin 2) L (capLift x)
  else T.map (sideLift x)

theorem prismMap_cap (b : Bool) {x : E} (hx : x ∈ prismCap b) :
    T.prismMap x = hamiltonMarkedProjection (Fin 1) (Fin 2) L (capLift x) := by
  have ht : x.2 = capHeight b := hx.2
  cases b <;> simp [prismMap, ht, capHeight]

theorem prismMap_side {x : E} (hx : x ∈ prismSide) :
    T.prismMap x = T.map (sideLift x) := by
  dsimp only [prismMap]
  split_ifs with ht
  · symm
    apply T.boundary_values
    refine ⟨?_, hx.1⟩
    rw [mem_sphere_zero_iff_norm]
    change ‖(fun _ : Fin 1 ↦ x.2)‖ = 1
    rw [pi_norm_const]
    rcases ht with ht | ht <;> rw [ht] <;> norm_num
  · rfl

theorem prismMap_cap_old_boundary (b : Bool) {x : E} (hx : x ∈ prismCap b) :
    T.prismMap x ∈ frontier (latticeHandleDomain (Fin 1) (Fin 2) L) := by
  rw [T.prismMap_cap b hx, latticeHandleDomain, frontier_prod_univ_eq,
    frontier_closedBall _ one_ne_zero]
  exact ⟨capLift_old_boundary b hx, mem_univ _⟩

theorem prismMap_injOn {h : OpenPartialHomeomorph (V1 × V2) V3}
    (retained : HamiltonRetainedBlockChart (Fin 1) (Fin 2) L e h) :
    InjOn T.prismMap (cubePrismBoundary (-1 : ℝ) 1) := by
  have hlift : Function.Injective capLift := by
    intro x y hxy
    have hfst : (3 / 2 : ℝ) • x.1 = (3 / 2 : ℝ) • y.1 := congrArg Prod.snd hxy
    have hfirst : x.1 = y.1 := by
      have hf := congrArg (fun z : V2 ↦ (2 / 3 : ℝ) • z) hfst
      simpa only [smul_smul, show (2 / 3 : ℝ) * (3 / 2) = 1 by norm_num,
        one_smul] using hf
    exact Prod.ext hfirst (congrArg (fun z : V1 × V2 ↦ z.1 0) hxy)
  have hcaps (b c : Bool) {x y : E} (hx : x ∈ prismCap b) (hy : y ∈ prismCap c)
      (hxy : T.prismMap x = T.prismMap y) : x = y := by
    rw [T.prismMap_cap b hx, T.prismMap_cap c hy] at hxy
    apply hlift (retained.quotient_injective ?_ ?_ hxy)
    · exact capLift_mem_block ⟨hx.1, (show x.2 = capHeight b from hx.2) ▸ capHeight_mem b⟩
    · exact capLift_mem_block ⟨hy.1, (show y.2 = capHeight c from hy.2) ▸ capHeight_mem c⟩
  have hside : InjOn T.prismMap prismSide := by
    intro x hx y hy hxy
    rw [T.prismMap_side hx, T.prismMap_side hy,
      T.map_eq ⟨sideLift x, sideLift_mem hx⟩,
      T.map_eq ⟨sideLift y, sideLift_mem hy⟩] at hxy
    have heq := congrArg Subtype.val (T.parametrization.injective (Subtype.ext hxy))
    exact Prod.ext (congrArg Prod.snd heq) (congrArg (fun z : V1 × V2 ↦ z.1 0) heq)
  have hcross (b : Bool) {x y : E} (hx : x ∈ prismCap b) (hy : y ∈ prismSide)
      (hxy : T.prismMap x = T.prismMap y) : x = y := by
    have hold : (T.parametrization ⟨sideLift y, sideLift_mem hy⟩ :
        LatticeHandleAmbient (Fin 1) (Fin 2) L) ∈
          frontier (latticeHandleDomain (Fin 1) (Fin 2) L) := by
      rw [← T.map_eq, ← T.prismMap_side hy, ← hxy]
      exact T.prismMap_cap_old_boundary b hx
    have hq := (T.old_boundary_iff ⟨sideLift y, sideLift_mem hy⟩).mp hold
    have habs : |y.2| = 1 := by
      rw [mem_sphere_zero_iff_norm] at hq
      change ‖(fun _ : Fin 1 ↦ y.2)‖ = 1 at hq
      simpa only [pi_norm_const, Real.norm_eq_abs] using hq
    have ht : y.2 = -1 ∨ y.2 = 1 := by
      rcases le_total 0 y.2 with ht | ht
      · exact Or.inr (by rwa [abs_of_nonneg ht] at habs)
      · exact Or.inl (by rw [abs_of_nonpos ht] at habs; linarith)
    rcases ht with ht | ht
    · exact hcaps b false hx ⟨sphere_subset_closedBall hy.1, ht⟩ hxy
    · exact hcaps b true hx ⟨sphere_subset_closedBall hy.1, ht⟩ hxy
  rw [prism_boundary_eq]
  intro x hx y hy hxy
  rcases hx with (hx | hx) | hx <;> rcases hy with (hy | hy) | hy
  · exact hcaps false false hx hy hxy
  · exact hcaps false true hx hy hxy
  · exact hcross false hx hy hxy
  · exact hcaps true false hx hy hxy
  · exact hcaps true true hx hy hxy
  · exact hcross true hx hy hxy
  · exact (hcross false hy hx hxy.symm).symm
  · exact (hcross true hy hx hxy.symm).symm
  · exact hside hx hy hxy

theorem prismMap_image :
    T.prismMap '' cubePrismBoundary (-1 : ℝ) 1 =
      T.surface ∪ hamiltonAttachingBlock (Fin 1) (Fin 2) L (3 / 2) := by
  have hside : T.prismMap '' prismSide = T.surface := by
    apply Subset.antisymm
    · rintro y ⟨x, hx, rfl⟩
      rw [T.prismMap_side hx, T.map_eq ⟨sideLift x, sideLift_mem hx⟩]
      exact (T.parametrization ⟨sideLift x, sideLift_mem hx⟩).property
    · intro y hy
      let x := T.parametrization.symm ⟨y, hy⟩
      have hxside : ((x : V1 × V2).2, (x : V1 × V2).1 0) ∈ prismSide := by
        refine ⟨x.property.2, abs_le.mp ?_⟩
        exact (norm_le_pi_norm (x : V1 × V2).1 0).trans
          (mem_closedBall_zero_iff.mp x.property.1)
      have hlift : sideLift ((x : V1 × V2).2, (x : V1 × V2).1 0) = x := by
        apply Prod.ext
        · funext i
          exact congrArg (x : V1 × V2).1 (Subsingleton.elim 0 i)
        · rfl
      refine ⟨((x : V1 × V2).2, (x : V1 × V2).1 0), hxside, ?_⟩
      rw [T.prismMap_side hxside, hlift, T.map_eq x]
      exact congrArg Subtype.val (T.parametrization.apply_symm_apply ⟨y, hy⟩)
  have hcaps : T.prismMap '' (prismCap false ∪ prismCap true) =
      hamiltonAttachingBlock (Fin 1) (Fin 2) L (3 / 2) := by
    apply Subset.antisymm
    · rintro y ⟨x, hx, rfl⟩
      have hcap (b : Bool) (hx : x ∈ prismCap b) :
          T.prismMap x ∈ hamiltonAttachingBlock (Fin 1) (Fin 2) L (3 / 2) := by
        rw [T.prismMap_cap b hx]
        refine ⟨capLift x, ⟨capLift_old_boundary b hx, ?_⟩, rfl⟩
        rw [mem_closedBall_zero_iff]
        change ‖(3 / 2 : ℝ) • x.1‖ ≤ 3 / 2
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
        have hn := mem_closedBall_zero_iff.mp hx.1
        linarith
      exact hx.elim (hcap false) (hcap true)
    · rintro y ⟨z, hz, rfl⟩
      have hzconst : z.1 = fun _ : Fin 1 ↦ z.1 0 :=
        funext fun i ↦ congrArg z.1 (Subsingleton.elim i 0)
      have ht : z.1 0 = -1 ∨ z.1 0 = 1 := by
        have hn := mem_sphere_zero_iff_norm.mp hz.1
        rw [hzconst, pi_norm_const, Real.norm_eq_abs] at hn
        rcases le_total 0 (z.1 0) with h | h
        · exact Or.inr (by rwa [abs_of_nonneg h] at hn)
        · exact Or.inl (by rw [abs_of_nonpos h] at hn; linarith)
      have hscaled : (2 / 3 : ℝ) • z.2 ∈ D := by
        rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
          abs_of_pos (by norm_num : (0 : ℝ) < 2 / 3)]
        have hn := mem_closedBall_zero_iff.mp hz.2
        linarith
      have hlift : capLift ((2 / 3 : ℝ) • z.2, z.1 0) = z := by
        apply Prod.ext
        · exact hzconst.symm
        · change (3 / 2 : ℝ) • ((2 / 3 : ℝ) • z.2) = z.2
          rw [smul_smul, show (3 / 2 : ℝ) * (2 / 3) = 1 by norm_num, one_smul]
      have hx : ((2 / 3 : ℝ) • z.2, z.1 0) ∈ prismCap false ∪ prismCap true := by
        exact ht.elim (fun h ↦ Or.inl ⟨hscaled, h⟩) (fun h ↦ Or.inr ⟨hscaled, h⟩)
      refine ⟨((2 / 3 : ℝ) • z.2, z.1 0), hx, ?_⟩
      rcases hx with hx | hx
      · rw [T.prismMap_cap false hx, hlift]
      · rw [T.prismMap_cap true hx, hlift]
  rw [prism_boundary_eq, image_union, hcaps, hside, union_comm]

end

end PoincareConjecture.M76.HamiltonProtectedDehnAnnulus
