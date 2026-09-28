import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Faces.CornerArcRectangle

set_option autoImplicit false

open Set Geometry TriangularRoofModel

namespace PoincareConjecture.M76.TriangleCorner

def cornerMap : Fin 3 → (ℝ × ℝ) →ᴬ[ℝ] ℝ × ℝ :=
  let X := (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap
  let Y := (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap
  let Z := ContinuousAffineMap.const ℝ (ℝ × ℝ) 1 - X - Y
  ![ContinuousAffineMap.id ℝ (ℝ × ℝ), Z.prod Y, X.prod Z]

@[simp] theorem cornerMap_zero (x : ℝ × ℝ) : cornerMap 0 x = x := rfl
@[simp] theorem cornerMap_one (x : ℝ × ℝ) : cornerMap 1 x = (1 - x.1 - x.2, x.2) := rfl
@[simp] theorem cornerMap_two (x : ℝ × ℝ) : cornerMap 2 x = (x.1, 1 - x.1 - x.2) := rfl

theorem cornerMap_involutive (c : Fin 3) : Function.Involutive (cornerMap c) := by
  intro x
  fin_cases c <;> ext <;> dsimp [cornerMap] <;> ring

def cornerHomeomorph (c : Fin 3) : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) where
  toFun := cornerMap c
  invFun := cornerMap c
  left_inv := cornerMap_involutive c
  right_inv := cornerMap_involutive c
  continuous_toFun := (cornerMap c).continuous
  continuous_invFun := (cornerMap c).continuous

theorem cornerMap_mem_base (c : Fin 3) (x : ℝ × ℝ) : cornerMap c x ∈ base ↔ x ∈ base := by
  simp only [base_eq_triangle, TriangleDiskModel.mem_right_region_iff]
  fin_cases c
  · rfl
  · dsimp [cornerMap]
    constructor <;> rintro ⟨h1, h2, h3⟩ <;> refine ⟨by linarith, by linarith, by linarith⟩
  · dsimp [cornerMap]
    constructor <;> rintro ⟨h1, h2, h3⟩ <;> refine ⟨by linarith, by linarith, by linarith⟩

theorem cornerMap_image_base (c : Fin 3) : cornerMap c '' base = base := by
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact (cornerMap_mem_base c x).mpr hx
  · intro x hx
    exact ⟨cornerMap c x, (cornerMap_mem_base c x).mpr hx, cornerMap_involutive c x⟩

theorem cornerMap_image_frontier (c : Fin 3) : cornerMap c '' frontier base = frontier base := by
  have h := (cornerHomeomorph c).image_frontier base
  change cornerMap c '' frontier base = frontier (cornerMap c '' base) at h
  rwa [cornerMap_image_base] at h

theorem cornerMap_mem_frontier (c : Fin 3) (x : ℝ × ℝ) :
    cornerMap c x ∈ frontier base ↔ x ∈ frontier base := by
  constructor
  · intro hx
    have h := (cornerMap_image_frontier c).subset (mem_image_of_mem (cornerMap c) hx)
    rwa [cornerMap_involutive] at h
  · exact fun hx => (cornerMap_image_frontier c).subset (mem_image_of_mem (cornerMap c) hx)

theorem corner_pair_unique {r : Set (ℝ × ℝ)} {c d : Fin 3} {a b u v : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    (hc : cornerMap c '' r = {(0, b), (a, 0)})
    (hd : cornerMap d '' r = {(0, v), (u, 0)}) : c = d := by
  have hpoint (z : ℝ × ℝ) (hz : z ∈ ({(0, b), (a, 0)} : Set (ℝ × ℝ))) :
      (cornerMap d (cornerMap c z)).1 = 0 ∨ (cornerMap d (cornerMap c z)).2 = 0 := by
    obtain ⟨x, hxr, hxz⟩ := hc.symm.subset hz
    have hx : x = cornerMap c z := by
      rw [← hxz, cornerMap_involutive]
    have h := hd.subset (mem_image_of_mem (cornerMap d) (hx ▸ hxr))
    rcases h with h | h
    · exact Or.inl (congrArg Prod.fst h)
    · exact Or.inr (congrArg Prod.snd (mem_singleton_iff.mp h))
  have hleft := hpoint (0, b) (by simp)
  have hbottom := hpoint (a, 0) (by simp)
  fin_cases c <;> fin_cases d
  all_goals first | rfl | skip
  all_goals dsimp [cornerMap] at hleft hbottom
  all_goals rcases hleft with hleft | hleft <;> rcases hbottom with hbottom | hbottom <;>
    rcases ha with ⟨ha0, ha1⟩ <;> rcases hb with ⟨hb0, hb1⟩ <;> exfalso <;> linarith

end PoincareConjecture.M76.TriangleCorner
