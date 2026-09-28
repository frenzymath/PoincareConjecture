import PoincareConjecture.Proofs.M01.Koszul

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.ConnectionExistence

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

noncomputable def koszulRHS (g : RiemannianMetric n M)
    (X Y Z : (x : M) → TangentSpace (𝓡 n) x) (x : M) : ℝ :=
  mvfderiv (𝓡 n) (fun y ↦ g.inner y (Y y) (Z y)) x (X x) +
  mvfderiv (𝓡 n) (fun y ↦ g.inner y (Z y) (X y)) x (Y x) -
  mvfderiv (𝓡 n) (fun y ↦ g.inner y (X y) (Y y)) x (Z x) +
  g.inner x (VectorField.mlieBracket (𝓡 n) X Y x) (Z x) -
  g.inner x (Y x) (VectorField.mlieBracket (𝓡 n) X Z x) -
  g.inner x (X x) (VectorField.mlieBracket (𝓡 n) Y Z x)

variable (g : RiemannianMetric n M)
  {X X' Y Y' Z Z' : (x : M) → TangentSpace (𝓡 n) x} {x : M}

theorem mdifferentiableAt_pair
    (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Y) x)
    (hZ : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Z) x) :
    MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) (fun y ↦ g.inner y (Y y) (Z y)) x := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact hY.inner_bundle hZ

theorem koszulRHS_add_test
    (hX : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% X) x)
    (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Y) x)
    (hZ : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Z) x)
    (hZ' : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Z') x) :
    koszulRHS g X Y (Z + Z') x = koszulRHS g X Y Z x + koszulRHS g X Y Z' x := by
  simp only [koszulRHS, Pi.add_apply, map_add, add_apply,
    mvfderiv_fun_add (mdifferentiableAt_pair g hY hZ) (mdifferentiableAt_pair g hY hZ'),
    mvfderiv_fun_add (mdifferentiableAt_pair g hZ hX) (mdifferentiableAt_pair g hZ' hX),
    VectorField.mlieBracket_add_right hZ hZ']
  ring

theorem koszulRHS_smul_test {f : M → ℝ}
    (hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f x)
    (hX : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% X) x)
    (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Y) x)
    (hZ : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Z) x) :
    koszulRHS g X Y (f • Z) x = f x * koszulRHS g X Y Z x := by
  simp only [koszulRHS, Pi.smul_apply', map_smul, smul_apply,
    smul_eq_mul, VectorField.mlieBracket_smul_right hf hZ, map_add,
    add_apply,
    mvfderiv_fun_mul hf (mdifferentiableAt_pair g hY hZ),
    mvfderiv_fun_mul hf (mdifferentiableAt_pair g hZ hX)]
  simp only [g.symm x]
  ring

theorem koszulRHS_add_direction
    (hX : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% X) x)
    (hX' : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% X') x)
    (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Y) x)
    (hZ : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Z) x) :
    koszulRHS g (X + X') Y Z x = koszulRHS g X Y Z x + koszulRHS g X' Y Z x := by
  simp only [koszulRHS, Pi.add_apply, map_add, add_apply,
    mvfderiv_fun_add (mdifferentiableAt_pair g hZ hX) (mdifferentiableAt_pair g hZ hX'),
    mvfderiv_fun_add (mdifferentiableAt_pair g hX hY) (mdifferentiableAt_pair g hX' hY),
    VectorField.mlieBracket_add_left hX hX']
  ring

theorem koszulRHS_smul_direction {f : M → ℝ}
    (hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f x)
    (hX : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% X) x)
    (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Y) x)
    (hZ : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Z) x) :
    koszulRHS g (f • X) Y Z x = f x * koszulRHS g X Y Z x := by
  simp only [koszulRHS, Pi.smul_apply', map_smul, smul_apply,
    smul_eq_mul, VectorField.mlieBracket_smul_left hf hX, map_add,
    add_apply,
    mvfderiv_fun_mul hf (mdifferentiableAt_pair g hZ hX),
    mvfderiv_fun_mul hf (mdifferentiableAt_pair g hX hY)]
  simp only [g.symm x]
  ring

theorem koszulRHS_add_field
    (hX : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% X) x)
    (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Y) x)
    (hY' : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Y') x)
    (hZ : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Z) x) :
    koszulRHS g X (Y + Y') Z x = koszulRHS g X Y Z x + koszulRHS g X Y' Z x := by
  simp only [koszulRHS, Pi.add_apply, map_add, add_apply,
    mvfderiv_fun_add (mdifferentiableAt_pair g hY hZ) (mdifferentiableAt_pair g hY' hZ),
    mvfderiv_fun_add (mdifferentiableAt_pair g hX hY) (mdifferentiableAt_pair g hX hY'),
    VectorField.mlieBracket_add_right hY hY', VectorField.mlieBracket_add_left hY hY']
  ring

theorem koszulRHS_smul_field {f : M → ℝ}
    (hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f x)
    (hX : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% X) x)
    (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Y) x)
    (hZ : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Z) x) :
    koszulRHS g X (f • Y) Z x = f x * koszulRHS g X Y Z x +
      2 * mvfderiv (𝓡 n) f x (X x) * g.inner x (Y x) (Z x) := by
  simp only [koszulRHS, Pi.smul_apply', map_smul, smul_apply,
    smul_eq_mul, VectorField.mlieBracket_smul_left hf hY,
    VectorField.mlieBracket_smul_right hf hY, map_add, add_apply,
    mvfderiv_fun_mul hf (mdifferentiableAt_pair g hY hZ),
    mvfderiv_fun_mul hf (mdifferentiableAt_pair g hX hY)]
  simp only [g.symm x]
  ring

theorem koszulRHS_swap_diff
    (_hX : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% X) x)
    (_hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Y) x)
    (_hZ : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Z) x) :
    koszulRHS g X Y Z x - koszulRHS g Y X Z x =
      2 * g.inner x (VectorField.mlieBracket (𝓡 n) X Y x) (Z x) := by
  have h₁ : (fun y ↦ g.inner y (X y) (Z y)) =
      (fun y ↦ g.inner y (Z y) (X y)) := by
    funext y; exact g.symm y _ _
  have h₂ : (fun y ↦ g.inner y (Y y) (X y)) =
      (fun y ↦ g.inner y (X y) (Y y)) := by
    funext y; exact g.symm y _ _
  have h₃ : (fun y ↦ g.inner y (Z y) (Y y)) =
      (fun y ↦ g.inner y (Y y) (Z y)) := by
    funext y; exact g.symm y _ _
  simp only [koszulRHS]
  rw [h₁, h₂, h₃, VectorField.mlieBracket_swap_apply]
  simp only [map_neg, neg_apply, g.symm x]
  ring

theorem koszulRHS_compat_sum
    (_hX : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% X) x)
    (_hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Y) x)
    (_hZ : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Z) x) :
    koszulRHS g X Y Z x + koszulRHS g X Z Y x =
      2 * mvfderiv (𝓡 n) (fun y ↦ g.inner y (Y y) (Z y)) x (X x) := by
  have h₁ : (fun y ↦ g.inner y (Z y) (X y)) =
      (fun y ↦ g.inner y (X y) (Z y)) := by
    funext y; exact g.symm y _ _
  have h₂ : (fun y ↦ g.inner y (X y) (Z y)) =
      (fun y ↦ g.inner y (Z y) (X y)) := by
    funext y; exact g.symm y _ _
  have h₃ : (fun y ↦ g.inner y (X y) (Y y)) =
      (fun y ↦ g.inner y (Y y) (X y)) := by
    funext y; exact g.symm y _ _
  have h₄ : (fun y ↦ g.inner y (Z y) (Y y)) =
      (fun y ↦ g.inner y (Y y) (Z y)) := by
    funext y; exact g.symm y _ _
  have hb₁ : VectorField.mlieBracket (𝓡 n) X Y x =
      -VectorField.mlieBracket (𝓡 n) Y X x :=
    VectorField.mlieBracket_swap_apply
  have hb₂ : VectorField.mlieBracket (𝓡 n) X Z x =
      -VectorField.mlieBracket (𝓡 n) Z X x :=
    VectorField.mlieBracket_swap_apply
  have hb₃ : VectorField.mlieBracket (𝓡 n) Z Y x =
      -VectorField.mlieBracket (𝓡 n) Y Z x :=
    VectorField.mlieBracket_swap_apply
  simp only [koszulRHS]
  rw [h₁, h₂, h₃, h₄, hb₁, hb₂, hb₃]
  simp only [map_neg, neg_apply, g.symm x]
  ring

end PoincareConjecture.ConnectionExistence
