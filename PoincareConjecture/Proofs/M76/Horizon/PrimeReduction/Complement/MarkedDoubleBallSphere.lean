import PoincareConjecture.Proofs.M76.Triangulation.CubeSphereLargeDisks
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallNormalization
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBoundaryPieceGluing
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages












set_option autoImplicit false

open Set Metric Geometry
open scoped BigOperators

namespace Geometry.CubicalThreeSphere

abbrev sphere : Set (Fin 4 → ℝ) := frontier (closedBall 0 1)

def lower : Set (Fin 4 → ℝ) := sphere ∩ {x | ∑ i, x i ≤ 0}

def upper : Set (Fin 4 → ℝ) := sphere ∩ {x | 0 ≤ ∑ i, x i}

def seam : Set (Fin 4 → ℝ) := sphere ∩ {x | ∑ i, x i = 0}

theorem lower_ball : IsFinitePLBallPair (Fin 3 → ℝ) lower seam := by
  exact isFinitePLBallPair_cube_frontier_cut (by norm_num) (by norm_num) (by simp)

private theorem neg_mem_sphere (x : Fin 4 → ℝ) : -x ∈ sphere ↔ x ∈ sphere := by
  simp [sphere, frontier_closedBall (0 : Fin 4 → ℝ) one_ne_zero]

theorem upper_ball : IsFinitePLBallPair (Fin 3 → ℝ) upper seam := by
  let a : (Fin 4 → ℝ) →ᴬ[ℝ] (Fin 4 → ℝ) :=
    -(ContinuousAffineMap.id ℝ (Fin 4 → ℝ))
  have ha : Function.Injective a := neg_injective
  have hl : a '' lower = upper := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change -y ∈ upper
      exact ⟨(neg_mem_sphere y).mpr hy.1, by simpa using hy.2⟩
    · intro hx
      refine ⟨-x, ⟨(neg_mem_sphere x).mpr hx.1, ?_⟩, ?_⟩
      · simpa using hx.2
      · change - -x = x
        exact neg_neg x
  have hs : a '' seam = seam := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change -y ∈ seam
      exact ⟨(neg_mem_sphere y).mpr hy.1, by simpa using hy.2⟩
    · intro hx
      refine ⟨-x, ⟨(neg_mem_sphere x).mpr hx.1, ?_⟩, ?_⟩
      · simpa using hx.2
      · change - -x = x
        exact neg_neg x
  simpa only [hl, hs] using lower_ball.affine_image a ha.injOn

theorem lower_inter_upper : lower ∩ upper = seam := by
  ext x
  simp only [lower, upper, seam, mem_inter_iff, mem_ofPred_eq]
  constructor
  · rintro ⟨⟨hx, hlo⟩, _, hhi⟩
    exact ⟨hx, le_antisymm hlo hhi⟩
  · rintro ⟨hx, hsum⟩
    exact ⟨⟨hx, hsum.le⟩, hx, hsum.ge⟩

theorem lower_union_upper : lower ∪ upper = sphere := by
  ext x
  constructor
  · rintro (hx | hx) <;> exact hx.1
  · intro hx
    rcases le_total (∑ i, x i) 0 with h | h
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr ⟨hx, h⟩

end Geometry.CubicalThreeSphere

namespace Set

open Geometry.CubicalThreeSphere

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]



theorem IsFinitePLBallPair.exists_marked_double_sphere_extension
    {b d q : Set E} (hb : IsFinitePLBallPair (Fin 3 → ℝ) b q)
    (hinter : b ∩ d = q) (e : d ≃ₜ upper) (he : e.IsFinitePL)
    (hmem : ∀ x : d, (x : E) ∈ q ↔ (e x : Fin 4 → ℝ) ∈ seam) :
    ∃ H : (b ∪ d : Set E) ≃ₜ sphere, H.IsFinitePL ∧
      (∀ x : d, (H ⟨x, Or.inr x.property⟩ : Fin 4 → ℝ) = e x) ∧
      (∀ x : (b ∪ d : Set E), (x : E) ∈ b ↔ (H x : Fin 4 → ℝ) ∈ lower) ∧
      (∀ x : (b ∪ d : Set E), (x : E) ∈ d ↔ (H x : Fin 4 → ℝ) ∈ upper) ∧
      (∀ x : (b ∪ d : Set E), (x : E) ∈ q ↔ (H x : Fin 4 → ℝ) ∈ seam) := by
  obtain ⟨H, hH, hkeep, hbH, hdH⟩ := hb.exists_union_homeomorph_of_boundary_piece
    lower_ball hinter lower_inter_upper e he hmem
  let G := H.trans (Homeomorph.setCongr lower_union_upper)
  refine ⟨G, hH.setCongr rfl lower_union_upper, ?_, hbH, hdH, ?_⟩
  · intro x
    exact congrArg (fun y : (lower ∪ upper : Set (Fin 4 → ℝ)) => (y : Fin 4 → ℝ))
      (hkeep x)
  · intro x
    rw [← hinter, ← lower_inter_upper]
    exact and_congr (hbH x) (hdH x)




theorem IsFinitePLBallPair.exists_sphere_model_of_three_ball_union
    {b d q : Set E} (hb : IsFinitePLBallPair (Fin 3 → ℝ) b q)
    (hd : IsFinitePLBallPair (Fin 3 → ℝ) d q) (hinter : b ∩ d = q) :
    ∃ H : (b ∪ d : Set E) ≃ₜ sphere, H.IsFinitePL ∧
      (∀ x : (b ∪ d : Set E), (x : E) ∈ b ↔ (H x : Fin 4 → ℝ) ∈ lower) ∧
      (∀ x : (b ∪ d : Set E), (x : E) ∈ d ↔ (H x : Fin 4 → ℝ) ∈ upper) ∧
      (∀ x : (b ∪ d : Set E), (x : E) ∈ q ↔ (H x : Fin 4 → ℝ) ∈ seam) := by
  obtain ⟨e, he, hmem⟩ := hd.exists_homeomorph upper_ball
  obtain ⟨H, hH, _, hbH, hdH, hqH⟩ :=
    hb.exists_marked_double_sphere_extension hinter e he hmem
  exact ⟨H, hH, hbH, hdH, hqH⟩

end Set
