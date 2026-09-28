import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.NeckAnalysis.TensorNorms
import PoincareConjecture.Proofs.M28.Mathlib.FiniteHessian.JetBounds










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle BigOperators Topology

namespace PoincareConjecture.Proofs.M28.NeckAnalysis

open FiniteHessian



theorem cylinder_component_sq_le_jet_error
    {u : ℝ} (hu : u < 1) (B : RoundCylinderTwoTensor) (z : RoundCylinderSpace)
    {k m : ℕ} (hk : k ≤ m) (a : Fin (2 + k) → Fin 3) :
    (roundCylinderIteratedDerivative u
      (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) B k (0, z.2) a) ^ 2 ≤
      roundCylinderJetErrorSquared u B m z / cylinderTensorWeight u a := by
  classical
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) z.1
  let T := roundCylinderIteratedDerivative u c B k (0, z.2)
  have horder : roundCylinderTensorNormSquared u c (0, z.2) T ≤
      roundCylinderJetErrorSquared u B m z := by
    have h := Finset.single_le_sum
      (f := fun j => roundCylinderTensorNormSquared u c (c z.1, z.2)
        (roundCylinderIteratedDerivative u c B j (c z.1, z.2)))
      (fun j _ => roundCylinderTensorNormSquared_nonneg hu z _)
      (Finset.mem_range.mpr (by omega : k < m + 1))
    simpa only [c, T, roundCylinderJetErrorSquared, sphere_chart_center] using h
  have hsquare : cylinderTensorWeight u a * T a ^ 2 ≤
      roundCylinderTensorNormSquared u c (0, z.2) T := by
    have h := roundCylinderTensorNormSquared_eq_sum hu z T
    rw [sphere_chart_center] at h
    rw [h]
    exact Finset.single_le_sum
      (fun b _ => mul_nonneg (cylinderTensorWeight_pos hu b).le
        (sq_nonneg _)) (Finset.mem_univ a)
  apply (le_div_iff₀ (cylinderTensorWeight_pos hu a)).mpr
  simpa only [mul_comm] using hsquare.trans horder



theorem cylinder_component_abs_le_of_jet_error_le_one
    {u : ℝ} (hu : u < 1) (B : RoundCylinderTwoTensor) (z : RoundCylinderSpace)
    {k m : ℕ} (hk : k ≤ m) (a : Fin (2 + k) → Fin 3)
    (herror : roundCylinderJetErrorSquared u B m z ≤ 1) :
    |roundCylinderIteratedDerivative u
      (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) B k (0, z.2) a| ≤
      Real.sqrt (1 / cylinderTensorWeight u a) := by
  have hw := cylinderTensorWeight_pos hu a
  have hsq := (cylinder_component_sq_le_jet_error hu B z hk a).trans
    (div_le_div_of_nonneg_right herror hw.le)
  apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [sq_abs, Real.sq_sqrt (by positivity : 0 ≤ 1 / cylinderTensorWeight u a)]
  exact hsq



theorem hasUniformZeroJetBoundsAt_roundCylinderIteratedDerivative
    {ι : Type*} (m : ℕ) (q : ι → UnitTwoSphere) (s : ι → ℝ)
    (B : ι → RoundCylinderTwoTensor)
    (herror : ∀ i, roundCylinderJetErrorSquared 0 (B i) m (q i, s i) ≤ 1)
    {k : ℕ} (hk : k ≤ m) (a : Fin (2 + k) → Fin 3) :
    HasUniformJetBoundsAt 0 (fun i p => roundCylinderIteratedDerivative 0
      (chartAt (EuclideanSpace ℝ (Fin 2)) (q i)) (B i) k p a)
      (fun i => (0, s i)) := by
  intro j hj
  have hj0 : j = 0 := by omega
  subst j
  refine ⟨Real.sqrt (1 / cylinderTensorWeight 0 a), fun i => ?_⟩
  simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using
    cylinder_component_abs_le_of_jet_error_le_one (by norm_num : (0 : ℝ) < 1)
      (B i) (q i, s i) hk a (herror i)

end PoincareConjecture.Proofs.M28.NeckAnalysis
