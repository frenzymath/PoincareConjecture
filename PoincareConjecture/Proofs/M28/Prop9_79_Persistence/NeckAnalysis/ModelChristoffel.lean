import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.NeckAnalysis.ModelGram

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators InnerProductSpace

namespace PoincareConjecture.Proofs.M28.NeckAnalysis

def cylinderSphereCoordinate (p : RoundCylinderCoordinates) : Fin 3 → ℝ :=
  ![p.1 0, p.1 1, 0]

def cylinderSphereDelta (a b : Fin 3) : ℝ :=
  if a = b ∧ a ≠ 2 then 1 else 0

noncomputable def cylinderModelChristoffel (p : RoundCylinderCoordinates)
    (a b d : Fin 3) : ℝ :=
  (-2 / (‖p.1‖ ^ 2 + 4)) *
    (cylinderSphereDelta a d * cylinderSphereCoordinate p b +
      cylinderSphereDelta a b * cylinderSphereCoordinate p d -
      cylinderSphereDelta b d * cylinderSphereCoordinate p a)

theorem roundCylinderChristoffel_chosen_chart {u : ℝ} (hu : u < 1)
    (q : UnitTwoSphere) (p : RoundCylinderCoordinates) (a b d : Fin 3) :
    roundCylinderChristoffel u (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b d =
      cylinderModelChristoffel p a b d := by
  have ht : 1 - u ≠ 0 := ne_of_gt (sub_pos.mpr hu)
  have hp : ‖p.1‖ ^ 2 + 4 ≠ 0 := by positivity
  unfold roundCylinderChristoffel
  rw [roundCylinderGram_inverse_chosen_chart hu]
  simp_rw [fderiv_roundCylinderGram_chosen_chart]
  fin_cases a <;> fin_cases b <;> fin_cases d <;>
    simp [Matrix.diagonal, roundCylinderCoordinateBasis,
      EuclideanSpace.inner_single_right, cylinderModelChristoffel,
      cylinderSphereDelta, cylinderSphereCoordinate, sphereChartConformalFactor] <;>
    field_simp [ht, hp] <;> ring

theorem contDiff_cylinderModelChristoffel (a b d : Fin 3) :
    ContDiff ℝ ∞ (fun p : RoundCylinderCoordinates => cylinderModelChristoffel p a b d) := by
  have hc (j : Fin 3) : ContDiff ℝ ∞
      (fun p : RoundCylinderCoordinates => cylinderSphereCoordinate p j) := by
    fin_cases j <;> dsimp [cylinderSphereCoordinate] <;> fun_prop
  have hr : ContDiff ℝ ∞
      (fun p : RoundCylinderCoordinates => -2 / (‖p.1‖ ^ 2 + 4)) :=
    contDiff_const.div (((contDiff_norm_sq ℝ).comp contDiff_fst).add contDiff_const)
      (fun _ => by positivity)
  have hcb : ContDiff ℝ ∞ (fun p =>
      cylinderSphereDelta a d * cylinderSphereCoordinate p b) := by
    convert ((contDiff_const : ContDiff ℝ ∞
      (fun _ : RoundCylinderCoordinates => cylinderSphereDelta a d)).smul (hc b)) using 1
    funext p
    simp [smul_eq_mul]
  have hcd : ContDiff ℝ ∞ (fun p =>
      cylinderSphereDelta a b * cylinderSphereCoordinate p d) := by
    convert ((contDiff_const : ContDiff ℝ ∞
      (fun _ : RoundCylinderCoordinates => cylinderSphereDelta a b)).smul (hc d)) using 1
    funext p
    simp [smul_eq_mul]
  have hca : ContDiff ℝ ∞ (fun p =>
      cylinderSphereDelta b d * cylinderSphereCoordinate p a) := by
    convert ((contDiff_const : ContDiff ℝ ∞
      (fun _ : RoundCylinderCoordinates => cylinderSphereDelta b d)).smul (hc a)) using 1
    funext p
    simp [smul_eq_mul]
  exact hr.mul ((hcb.add hcd).sub hca)

theorem iteratedFDeriv_cylinderModelChristoffel_axial (k : ℕ) (s : ℝ)
    (a b d : Fin 3) :
    iteratedFDeriv ℝ k (fun p => cylinderModelChristoffel p a b d) (0, s) =
      iteratedFDeriv ℝ k (fun p => cylinderModelChristoffel p a b d) 0 := by
  have heq : (fun p : RoundCylinderCoordinates =>
      cylinderModelChristoffel ((0, s) + p) a b d) =
      (fun p => cylinderModelChristoffel p a b d) := by
    funext p
    simp [cylinderModelChristoffel, cylinderSphereCoordinate]
  have h := iteratedFDeriv_comp_add_left (𝕜 := ℝ)
    (f := fun p => cylinderModelChristoffel p a b d) k (0, s) 0
  rw [heq, add_zero] at h
  exact h.symm

theorem exists_bound_roundCylinderChristoffel_jets (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : ℝ), u < 1 → ∀ (q : UnitTwoSphere) (s : ℝ),
      ∀ k ≤ m, ∀ a b d : Fin 3,
      ‖iteratedFDeriv ℝ k
        (fun p => roundCylinderChristoffel u
          (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b d) (0, s)‖ ≤ C := by
  let value : Fin (m + 1) × Fin 3 × Fin 3 × Fin 3 → ℝ := fun i =>
    ‖iteratedFDeriv ℝ i.1 (fun p =>
      cylinderModelChristoffel p i.2.1 i.2.2.1 i.2.2.2) 0‖
  refine ⟨∑ i, value i, Finset.sum_nonneg (fun _ _ => norm_nonneg _), ?_⟩
  intro u hu q s k hkm a b d
  simp_rw [roundCylinderChristoffel_chosen_chart hu]
  rw [iteratedFDeriv_cylinderModelChristoffel_axial]
  exact Finset.single_le_sum (f := value) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ (⟨k, Nat.lt_succ_of_le hkm⟩, a, b, d))

end PoincareConjecture.Proofs.M28.NeckAnalysis
