import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexTwoStandardPrism
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexTwoMarkedBall
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLImageTriangulation










set_option autoImplicit false

open Set Metric Geometry CoordinateHalfBoxes

namespace PoincareConjecture.M76.HamiltonIndexTwoStandard

local notation "P" => ((ℝ × ℝ) × ℝ)
local notation "V" => (Fin 3 → ℝ)

private def coordinateLinear : P ≃ₗ[ℝ] V where
  toFun p := ![p.1.1, p.1.2, p.2]
  invFun x := ((x 0, x 1), x 2)
  left_inv _ := rfl
  right_inv x := by ext i; fin_cases i <;> rfl
  map_add' p q := by ext i; fin_cases i <;> rfl
  map_smul' r p := by ext i; fin_cases i <;> rfl



noncomputable def coordinates : P ≃ᴬ[ℝ] V :=
  coordinateLinear.toContinuousLinearEquiv.toContinuousAffineEquiv


theorem coordinates_apply (p : P) : coordinates p = ![p.1.1, p.1.2, p.2] := rfl



noncomputable def endHeight (j : Bool) : ℝ := if j then 3 / 2 else -(3 / 2)


def lowerBound : V := ![-1, -1, -2]


def upperBound : V := ![1, 1, 2]


def side : Set V := coordinates '' band (-(3 / 2)) (3 / 2)


def outer (j : Bool) : Set V := coordinates ''
  if j then upperOuter (3 / 2) 2 else lowerOuter (-2) (-(3 / 2))


def rim (j : Bool) : Set V := coordinates '' endRim (endHeight j)



theorem box_image : coordinates '' prism (-2) 2 = Icc lowerBound upperBound := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    change (p.1.1 ∈ Icc (-1 : ℝ) 1 ∧ p.1.2 ∈ Icc (-1 : ℝ) 1) ∧
      p.2 ∈ Icc (-2 : ℝ) 2 at hp
    constructor
    · intro i
      fin_cases i
      · exact hp.1.1.1
      · exact hp.1.2.1
      · exact hp.2.1
    · intro i
      fin_cases i
      · exact hp.1.1.2
      · exact hp.1.2.2
      · exact hp.2.2
  · intro hx
    refine ⟨((x 0, x 1), x 2), ?_, ?_⟩
    · exact ⟨⟨⟨hx.1 0, hx.2 0⟩, ⟨hx.1 1, hx.2 1⟩⟩, ⟨hx.1 2, hx.2 2⟩⟩
    · ext i
      fin_cases i <;> rfl

private theorem outer_height_bounds (j : Bool) {p : P}
    (hp : p ∈ if j then upperOuter (3 / 2) 2 else lowerOuter (-2) (-(3 / 2))) :
    if j then (3 / 2 : ℝ) ≤ p.2 ∧ p.2 ≤ 2 else
      (-2 : ℝ) ≤ p.2 ∧ p.2 ≤ -(3 / 2) := by
  cases j with
  | false =>
      rcases hp with hp | hp
      · exact hp.2
      · rw [show p.2 = -2 from hp.2]
        norm_num
  | true =>
      rcases hp with hp | hp
      · exact hp.2
      · rw [show p.2 = 2 from hp.2]
        norm_num

private theorem standard_boundary_partition :
    ((band (-2) 2 ∪ endDisk (-2)) ∪ endDisk 2) =
      (band (-(3 / 2)) (3 / 2) ∪ lowerOuter (-2) (-(3 / 2))) ∪
        upperOuter (3 / 2) 2 := by
  ext p
  constructor
  · rintro ((hp | hp) | hp)
    · by_cases hlo : p.2 ≤ -(3 / 2 : ℝ)
      · exact Or.inl (Or.inr (Or.inl ⟨hp.1, hp.2.1, hlo⟩))
      · by_cases hhi : (3 / 2 : ℝ) ≤ p.2
        · exact Or.inr (Or.inl ⟨hp.1, hhi, hp.2.2⟩)
        · exact Or.inl (Or.inl ⟨hp.1, (lt_of_not_ge hlo).le, (lt_of_not_ge hhi).le⟩)
    · exact Or.inl (Or.inr (Or.inr hp))
    · exact Or.inr (Or.inr hp)
  · rintro ((hp | hp) | hp)
    · exact Or.inl (Or.inl ⟨hp.1, by linarith [hp.2.1], by linarith [hp.2.2]⟩)
    · rcases hp with hp | hp
      · exact Or.inl (Or.inl ⟨hp.1, hp.2.1, by linarith [hp.2.2]⟩)
      · exact Or.inl (Or.inr hp)
    · rcases hp with hp | hp
      · exact Or.inl (Or.inl ⟨hp.1, by linarith [hp.2.1], hp.2.2⟩)
      · exact Or.inr hp




noncomputable def frame : HamiltonIndexTwoFrame (Fin 3) := by
  have hbox := (prism_ballPair (by norm_num : (-2 : ℝ) < 2)).affine_image
    coordinates.toContinuousAffineMap coordinates.injective.injOn
  change IsFinitePLBallPair P (coordinates '' prism (-2) 2)
    (coordinates '' ((band (-2) 2 ∪ endDisk (-2)) ∪ endDisk 2)) at hbox
  rw [box_image] at hbox
  have hfront := hbox.frontier_eq_of_finrank_eq (by simp [Module.finrank_prod])
  refine {
    lower := lowerBound
    upper := upperBound
    side := side
    outer := outer
    rim := rim
    boxBall := ?_
    outerBall := ?_
    outerDisjoint := ?_
    frontier_eq := ?_
    topRimNonempty := ?_
    sidePL := ?_
  }
  · rwa [hfront]
  · intro j
    cases j with
    | false =>
        exact (lowerOuter_ballPair (by norm_num : (-2 : ℝ) < -(3 / 2))).affine_image
          coordinates.toContinuousAffineMap coordinates.injective.injOn
    | true =>
        exact (upperOuter_ballPair (by norm_num : (3 / 2 : ℝ) < 2)).affine_image
          coordinates.toContinuousAffineMap coordinates.injective.injOn
  · apply Set.disjoint_left.mpr
    rintro x ⟨p, hp, rfl⟩ ⟨q, hq, heq⟩
    have hqp : q = p := coordinates.injective heq
    subst q
    have hlo := outer_height_bounds false hp
    have hhi := outer_height_bounds true hq
    norm_num only [Bool.false_eq_true, if_false, if_true] at hlo hhi
    linarith [hlo.2, hhi.1]
  · rw [hfront, standard_boundary_partition]
    simp only [image_union, side, outer, Bool.false_eq_true, if_false, if_true]
  · refine ⟨coordinates ((1, 0), (3 / 2)), mem_image_of_mem coordinates ?_⟩
    norm_num [endRim, baseBoundary, endHeight]
  · have hmap := (band_identity_finitePL
      (by norm_num : -(3 / 2 : ℝ) < 3 / 2)).postcomp coordinates.toContinuousAffineMap
    obtain ⟨K, hK, hKs⟩ := hmap.exists_finite_triangulation_image
    exact ⟨K, hK, hKs, K.affineOnFaces_affine (ContinuousAffineMap.id ℝ V)⟩

end PoincareConjecture.M76.HamiltonIndexTwoStandard
