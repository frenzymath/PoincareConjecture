import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexTwoCoverCoordinates
import PoincareConjecture.Proofs.M76.Mathlib.HamiltonHandleCubeBall

set_option autoImplicit false

open Set Metric Geometry CoordinateHalfBoxes

namespace PoincareConjecture.M76.HamiltonIndexTwoStandard

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

private noncomputable def diskAffine (b : Bool) : V2 →ᴬ[ℝ] V3 :=
  coordinates.toContinuousAffineMap.comp
    ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).toContinuousLinearMap.toContinuousAffineMap.prod
      (ContinuousAffineMap.const ℝ V2 (endHeight b)))

private theorem diskAffine_apply (b : Bool) (x : V2) :
    diskAffine b x = ![x 0, x 1, endHeight b] := rfl

private theorem diskAffine_image (b : Bool) :
    diskAffine b '' closedBall (0 : V2) 1 = source.disk b := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hb (i : Fin 2) : |x i| ≤ 1 := by
      simpa only [Real.norm_eq_abs] using
        (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mp
          (mem_closedBall_zero_iff.mp hx) i
    exact ⟨((x 0, x 1), endHeight b),
      ⟨⟨abs_le.mp (hb 0), abs_le.mp (hb 1)⟩, rfl⟩, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    change p.1 ∈ base 1 ∧ p.2 = endHeight b at hp
    refine ⟨![p.1.1, p.1.2], ?_, ?_⟩
    · apply mem_closedBall_zero_iff.mpr
      apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
      intro i
      fin_cases i
      · exact Real.norm_eq_abs _ ▸ abs_le.mpr hp.1.1
      · exact Real.norm_eq_abs _ ▸ abs_le.mpr hp.1.2
    · rw [diskAffine_apply, coordinates_apply, hp.2]
      rfl

private theorem diskAffine_injective (b : Bool) : Function.Injective (diskAffine b) := by
  intro x y h
  funext i
  fin_cases i
  · exact congrFun h 0
  · exact congrFun h 1

private theorem diskAffine_finitePL (b : Bool) :
    FinitePiecewiseAffineOn (diskAffine b) (closedBall (0 : V2) 1) := by
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKC, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_unit_cube (ι := Fin 2)
  exact ⟨K, hK, hKC, K.affineOnFaces_affine (diskAffine b)⟩

theorem exists_standard_disk_parameter (b : Bool) :
    ∃ e : closedBall (0 : V2) 1 ≃ₜ source.disk b,
      e.IsFinitePL ∧
      (∀ x : closedBall (0 : V2) 1,
        (e x : V3) = ![x.val 0, x.val 1, endHeight b]) ∧
      (∀ x : closedBall (0 : V2) 1,
        (e x : V3) ∈ rim b ↔ (x : V2) ∈ sphere (0 : V2) 1) := by
  obtain ⟨f, _, hfval⟩ := (diskAffine_finitePL b).exists_homeomorph_image
    (diskAffine_injective b).injOn
  let e := f.trans (Homeomorph.setCongr (diskAffine_image b))
  have heval (x : closedBall (0 : V2) 1) : (e x : V3) = diskAffine b x := hfval x
  refine ⟨e, ⟨diskAffine b, diskAffine_finitePL b, heval⟩,
    fun x => (heval x).trans (diskAffine_apply b x), ?_⟩
  intro x
  have hbound (i : Fin 2) : |x.val i| ≤ 1 := by
    simpa only [Real.norm_eq_abs] using
      (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mp
        (mem_closedBall_zero_iff.mp x.property) i
  have hnorm : ‖(x : V2)‖ ≤ 1 := mem_closedBall_zero_iff.mp x.property
  rw [heval]
  change coordinates ((x.val 0, x.val 1), endHeight b) ∈
    coordinates '' endRim (endHeight b) ↔ (x : V2) ∈ sphere (0 : V2) 1
  rw [coordinates.injective.mem_set_image]
  change (x.val 0, x.val 1) ∈ baseBoundary 1 ∧ endHeight b = endHeight b ↔ _
  simp only [and_true, baseBoundary, mem_union, mem_prod, mem_insert_iff,
    mem_singleton_iff, mem_Icc]
  rw [mem_sphere_zero_iff_norm]
  constructor
  · rintro (⟨hx, _⟩ | ⟨_, hx⟩)
    · have hle := norm_le_pi_norm (x : V2) 0
      rcases hx with hx | hx <;> rw [hx] at hle <;> norm_num at hle <;> linarith
    · have hle := norm_le_pi_norm (x : V2) 1
      rcases hx with hx | hx <;> rw [hx] at hle <;> norm_num at hle <;> linarith
  · intro hx
    by_cases hzero : x.val 0 = -1 ∨ x.val 0 = 1
    · exact Or.inl ⟨hzero, abs_le.mp (hbound 1)⟩
    by_cases hone : x.val 1 = -1 ∨ x.val 1 = 1
    · exact Or.inr ⟨abs_le.mp (hbound 0), hone⟩
    have hlt : ‖(x : V2)‖ < 1 := by
      apply (pi_norm_lt_iff (by norm_num : (0 : ℝ) < 1)).mpr
      intro i
      fin_cases i
      · rw [Real.norm_eq_abs, abs_lt]
        have hb := abs_le.mp (hbound 0)
        push Not at hzero
        exact ⟨lt_of_le_of_ne hb.1 hzero.1.symm, lt_of_le_of_ne hb.2 hzero.2⟩
      · rw [Real.norm_eq_abs, abs_lt]
        have hb := abs_le.mp (hbound 1)
        push Not at hone
        exact ⟨lt_of_le_of_ne hb.1 hone.1.symm, lt_of_le_of_ne hb.2 hone.2⟩
    linarith

end PoincareConjecture.M76.HamiltonIndexTwoStandard
