import PoincareConjecture.Proofs.M34.Standard.NeckMetricComparisonCoordinates
import PoincareConjecture.Proofs.M34.Mathlib.MatrixInverseSmoothOn
import PoincareConjecture.Proofs.M34.Prop12_7_Asymptotics.CylinderJetTranslation











set_option autoImplicit false

open Set
open scoped Manifold ContDiff BigOperators

namespace PoincareConjecture.M34

local notation "E₂" => EuclideanSpace ℝ (Fin 2)



theorem capPersistence_modelGram_contDiff {m : ℕ∞ω} (u : ℝ)
    (q : UnitTwoSphere) (a b : Fin 3) :
    ContDiff ℝ m (fun p : RoundCylinderCoordinates =>
      roundCylinderGram u (chartAt E₂ q) p a b) := by
  have hf : ContDiff ℝ m (fun p : RoundCylinderCoordinates =>
      2 * (1 - u) * (16 / (‖p.1‖ ^ 2 + 4) ^ 2)) :=
    contDiff_const.mul (contDiff_const.div
      ((((contDiff_norm_sq ℝ).comp contDiff_fst).add contDiff_const).pow 2)
      (fun _ => by positivity))
  simp only [roundCylinderGram_chosenChart, Matrix.diagonal_apply]
  by_cases hab : a = b
  · subst b
    fin_cases a
    · exact hf
    · exact hf
    · exact contDiff_const
  · simp only [if_neg hab]
    exact contDiff_const



theorem capPersistence_modelGram_det_ne_zero {u : ℝ} (hu : u < 1)
    (q : UnitTwoSphere) (p : RoundCylinderCoordinates) :
    (roundCylinderGram u (chartAt E₂ q) p).det ≠ 0 := by
  rw [roundCylinderGram_chosenChart, Matrix.det_diagonal]
  have hp : 0 < 2 * (1 - u) * (16 / (‖p.1‖ ^ 2 + 4) ^ 2) := by positivity
  apply (Finset.prod_pos fun i _ => ?_).ne'
  fin_cases i
  · exact hp
  · exact hp
  · norm_num



theorem capPersistence_modelChristoffel_contDiff {m : ℕ∞ω} {u : ℝ}
    (hu : u < 1) (q : UnitTwoSphere) (a b d : Fin 3) :
    ContDiff ℝ m (fun p : RoundCylinderCoordinates =>
      roundCylinderChristoffel u (chartAt E₂ q) p a b d) := by
  have hinv (i j : Fin 3) : ContDiff ℝ m (fun p : RoundCylinderCoordinates =>
      (roundCylinderGram u (chartAt E₂ q) p)⁻¹ i j) := by
    apply contDiffOn_univ.mp
    exact ContDiffOn.matrix_inv
      (fun l k => (capPersistence_modelGram_contDiff (m := m) u q l k).contDiffOn)
      (fun p _ => capPersistence_modelGram_det_ne_zero hu q p) i j
  have hd (i j k : Fin 3) : ContDiff ℝ m (fun p : RoundCylinderCoordinates =>
      fderiv ℝ (fun y => roundCylinderGram u (chartAt E₂ q) y i j) p
        (roundCylinderCoordinateBasis k)) :=
    ((capPersistence_modelGram_contDiff (m := m + 1) u q i j).fderiv_right
      (m := m) le_rfl).clm_apply contDiff_const
  unfold roundCylinderChristoffel
  exact contDiff_const.mul (ContDiff.sum fun j _ =>
    (hinv a j).mul (((hd d j b).add (hd b j d)).sub (hd b d j)))



theorem capPersistence_modelChristoffel_eq (u : ℝ) (q q' : UnitTwoSphere) :
    roundCylinderChristoffel u (chartAt E₂ q) =
      roundCylinderChristoffel u (chartAt E₂ q') := by
  funext p a b d
  simp only [roundCylinderChristoffel, roundCylinderGram_chosenChart]



theorem capPersistence_exists_modelChristoffel_jet_bound {u : ℝ} (hu : u < 1)
    {K : Set RoundCylinderCoordinates} (hK : IsCompact K) (N : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ q : UnitTwoSphere, ∀ x ∈ K, ∀ j ≤ N,
      ∀ a b d : Fin 3, ‖iteratedFDeriv ℝ j (fun y =>
        roundCylinderChristoffel u (chartAt E₂ q) y a b d) x‖ ≤ D := by
  classical
  let q₀ : UnitTwoSphere := ⟨EuclideanSpace.single 0 1, by simp⟩
  have hb (i : Fin (N + 1) × Fin 3 × Fin 3 × Fin 3) : ∃ C : ℝ,
      ∀ x ∈ K, ‖iteratedFDeriv ℝ i.1.val (fun y =>
        roundCylinderChristoffel u (chartAt E₂ q₀) y i.2.1 i.2.2.1 i.2.2.2) x‖ ≤ C := by
    apply hK.exists_bound_of_continuousOn
    have hs := capPersistence_modelChristoffel_contDiff (m := ∞)
      hu q₀ i.2.1 i.2.2.1 i.2.2.2
    exact (hs.continuous_iteratedFDeriv (by exact_mod_cast le_top)).continuousOn
  choose C hC using hb
  let D : ℝ := ∑ i : Fin (N + 1) × Fin 3 × Fin 3 × Fin 3, max (C i) 0
  refine ⟨D, Finset.sum_nonneg (fun _ _ => le_max_right _ _), ?_⟩
  intro q x hx j hj a b d
  rw [capPersistence_modelChristoffel_eq u q q₀]
  let i : Fin (N + 1) × Fin 3 × Fin 3 × Fin 3 :=
    (⟨j, Nat.lt_succ_of_le hj⟩, a, b, d)
  exact (hC i x hx).trans ((le_max_left _ _).trans
    (Finset.single_le_sum (fun _ _ => le_max_right _ _) (Finset.mem_univ i)))



theorem capPersistence_modelChristoffel_jet_add_axial (s u : ℝ)
    (q : UnitTwoSphere) (p : RoundCylinderCoordinates) (j : ℕ) (a b d : Fin 3) :
    iteratedFDeriv ℝ j (fun y => roundCylinderChristoffel u (chartAt E₂ q) y a b d)
        (p + (0, s)) =
      iteratedFDeriv ℝ j (fun y => roundCylinderChristoffel u (chartAt E₂ q) y a b d) p := by
  rw [← iteratedFDeriv_comp_add_right j (0, s)]
  congr 1
  funext y
  exact roundCylinderChristoffel_add_axial s u _ y a b d



theorem capPersistence_exists_modelChristoffel_center_jet_bound
    {u : ℝ} (hu : u < 1) (N : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (q : UnitTwoSphere) (s : ℝ), ∀ j ≤ N,
      ∀ a b d : Fin 3, ‖iteratedFDeriv ℝ j (fun y =>
        roundCylinderChristoffel u (chartAt E₂ q) y a b d) (chartAt E₂ q q, s)‖ ≤ D := by
  obtain ⟨D, hD, hDb⟩ := capPersistence_exists_modelChristoffel_jet_bound
    hu (isCompact_singleton (x := (0 : RoundCylinderCoordinates))) N
  refine ⟨D, hD, ?_⟩
  intro q s j hj a b d
  rw [sphere_chart_center_zero]
  have he := capPersistence_modelChristoffel_jet_add_axial s u q 0 j a b d
  simpa only [zero_add] using
    (congrArg norm he).le.trans (hDb q 0 (mem_singleton _) j hj a b d)

end PoincareConjecture.M34
