import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceCylinderModelJets











set_option autoImplicit false

open Set
open scoped Manifold ContDiff BigOperators

namespace PoincareConjecture.M34

local notation "E₂" => EuclideanSpace ℝ (Fin 2)



theorem capNeckNormalization_modelGram_center_jet_eq
    (u : ℝ) (q q₀ : UnitTwoSphere) (s : ℝ) (j : ℕ) (a b : Fin 3) :
    iteratedFDeriv ℝ j (fun y => roundCylinderGram u (chartAt E₂ q) y a b) (0, s) =
      iteratedFDeriv ℝ j (fun y => roundCylinderGram u (chartAt E₂ q₀) y a b) 0 := by
  have hshift : iteratedFDeriv ℝ j (fun y =>
      roundCylinderGram u (chartAt E₂ q) y a b) (0, s) =
      iteratedFDeriv ℝ j (fun y => roundCylinderGram u (chartAt E₂ q) y a b) 0 := by
    have h := iteratedFDeriv_comp_add_right (𝕜 := ℝ) j
      (f := fun y => roundCylinderGram u (chartAt E₂ q) y a b)
      (x := (0 : RoundCylinderCoordinates)) (0, s)
    have heq : (fun y => roundCylinderGram u (chartAt E₂ q) (y + (0, s)) a b) =
        fun y => roundCylinderGram u (chartAt E₂ q) y a b := by
      funext y
      exact congrFun (congrFun (roundCylinderGram_add_axial s u _ y) a) b
    rw [heq, zero_add] at h
    exact h.symm
  have hcenter : (fun y => roundCylinderGram u (chartAt E₂ q) y a b) =
      fun y => roundCylinderGram u (chartAt E₂ q₀) y a b := by
    funext y
    simp only [roundCylinderGram_chosenChart]
  rw [hshift, hcenter]



theorem capNeckNormalization_exists_modelGram_center_jet_bound (u : ℝ) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : UnitTwoSphere) (s : ℝ), ∀ j ≤ m,
      ∀ a b : Fin 3, ‖iteratedFDeriv ℝ j (fun y =>
        roundCylinderGram u (chartAt E₂ q) y a b) (0, s)‖ ≤ C := by
  classical
  let q₀ : UnitTwoSphere := ⟨EuclideanSpace.single 0 1, by simp⟩
  let F : Fin (m + 1) × Fin 3 × Fin 3 → ℝ := fun i =>
    ‖iteratedFDeriv ℝ i.1.val (fun y =>
      roundCylinderGram u (chartAt E₂ q₀) y i.2.1 i.2.2) 0‖
  obtain ⟨C, hC⟩ := (Set.finite_range F).bddAbove
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro q s j hj a b
  rw [capNeckNormalization_modelGram_center_jet_eq u q q₀ s j a b]
  let i : Fin (m + 1) × Fin 3 × Fin 3 := (⟨j, Nat.lt_succ_of_le hj⟩, a, b)
  exact (hC (mem_range_self i)).trans (le_max_left _ _)



theorem capNeckNormalization_shift_mem {delta epsilon s : ℝ}
    (hdelta : 0 < delta) (hde : delta ≤ epsilon)
    (hs : s ∈ Ioo (-epsilon⁻¹) epsilon⁻¹) :
    s + (epsilon⁻¹ - delta⁻¹) ∈ Ioo (-delta⁻¹) delta⁻¹ := by
  have hinv := inv_anti₀ hdelta hde
  constructor <;> linarith [hs.1, hs.2]

end PoincareConjecture.M34

namespace PoincareConjecture



theorem RoundCylinderTensorSmoothOn.shift_of_mapsTo {delta epsilon c : ℝ}
    {B : RoundCylinderTwoTensor} (hB : RoundCylinderTensorSmoothOn delta B)
    (hmap : ∀ s ∈ Ioo (-epsilon⁻¹) epsilon⁻¹,
      s + c ∈ Ioo (-delta⁻¹) delta⁻¹) :
    RoundCylinderTensorSmoothOn epsilon (M34.roundCylinderShift c B) := by
  intro q a b
  have heq : (fun p => roundCylinderTensorCoefficient (M34.roundCylinderShift c B)
      (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b) =
      (fun p => roundCylinderTensorCoefficient B
        (chartAt (EuclideanSpace ℝ (Fin 2)) q) (p + (0, c)) a b) := by
    funext p
    exact M34.roundCylinderTensorCoefficient_shift c B _ p a b
  rw [heq]
  exact (hB q a b).comp (contDiff_id.add contDiff_const).contDiffOn
    (fun p hp => ⟨by simpa using hp.1, hmap p.2 hp.2⟩)



theorem RoundCylinderTensorSmoothOn.const_mul {epsilon beta : ℝ}
    {B : RoundCylinderTwoTensor} (hB : RoundCylinderTensorSmoothOn epsilon B) :
    RoundCylinderTensorSmoothOn epsilon (fun z v w => beta * B z v w) := by
  intro q a b
  exact contDiffOn_const.mul (hB q a b)

end PoincareConjecture
