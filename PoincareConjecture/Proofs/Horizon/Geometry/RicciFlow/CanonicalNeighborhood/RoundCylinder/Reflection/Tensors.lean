import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.RoundCylinder.Reflection.Connection


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.RoundCylinderReflection

def weight {r : ℕ} (a : Fin r → Fin 3) : ℝ := ∏ i, sign (a i)

@[simp] theorem weight_mul_self {r : ℕ} (a : Fin r → Fin 3) :
    weight a * weight a = 1 := by
  simp only [weight, ← Finset.prod_mul_distrib, sign_mul_self, Finset.prod_const_one]

@[simp] theorem weight_sq {r : ℕ} (a : Fin r → Fin 3) : weight a ^ 2 = 1 := by
  simpa only [pow_two] using weight_mul_self a

theorem weight_succ {r : ℕ} (a : Fin (r + 1) → Fin 3) :
    weight a = sign (a 0) * weight (fun i => a i.succ) := Fin.prod_univ_succ _

theorem weight_update {r : ℕ} (a : Fin r → Fin 3) (i : Fin r) (j : Fin 3) :
    weight (Function.update a i j) = sign j * sign (a i) * weight a := by
  classical
  have hf : (fun k => sign (Function.update a i j k)) =
      Function.update (fun k => sign (a k)) i (sign j) := by
    funext k
    by_cases h : k = i <;> simp [h]
  unfold weight
  rw [hf, Finset.prod_update_of_mem (Finset.mem_univ i)]
  rw [← Finset.mul_prod_erase Finset.univ (fun k => sign (a k)) (Finset.mem_univ i)]
  simp only [Finset.sdiff_singleton_eq_erase]
  calc
    sign j * ∏ x ∈ Finset.univ.erase i, sign (a x) =
        sign j * (sign (a i) * sign (a i)) *
          ∏ x ∈ Finset.univ.erase i, sign (a x) := by rw [sign_mul_self, mul_one]
    _ = _ := by ring

noncomputable def tensor {r : ℕ} (T : RoundCylinderCoordinates → (Fin r → Fin 3) → ℝ) :
    RoundCylinderCoordinates → (Fin r → Fin 3) → ℝ :=
  fun p a => weight a * T (coordinates p) a

theorem derivative_tensor (u : ℝ)
    (c : OpenPartialHomeomorph UnitTwoSphere (EuclideanSpace ℝ (Fin 2)))
    {r : ℕ} (T : RoundCylinderCoordinates → (Fin r → Fin 3) → ℝ)
    (p : RoundCylinderCoordinates) (a : Fin (r + 1) → Fin 3) :
    roundCylinderTensorDerivative u c (tensor T) p a =
      weight a * roundCylinderTensorDerivative u c T (coordinates p) a := by
  unfold roundCylinderTensorDerivative tensor
  rw [fderiv_const_mul_reflect _ (fun q => T q (fun i => a i.succ)) p (a 0),
    weight_succ, mul_sub]
  congr 1
  · ring
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [christoffel_parity u c p j (a 0) (a i.succ), weight_update]
    ring_nf
    simp only [sign_sq, mul_one, one_mul]

theorem normSquared_tensor (u : ℝ)
    (c : OpenPartialHomeomorph UnitTwoSphere (EuclideanSpace ℝ (Fin 2)))
    {r : ℕ} (T : RoundCylinderCoordinates → (Fin r → Fin 3) → ℝ)
    (p : RoundCylinderCoordinates) :
    roundCylinderTensorNormSquared u c p (tensor T p) =
      roundCylinderTensorNormSquared u c (coordinates p) (T (coordinates p)) := by
  unfold roundCylinderTensorNormSquared tensor
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp_rw [inverseGram_parity u c p]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  change (weight a * weight b * _) * (weight a * _) * (weight b * _) = _
  ring_nf
  simp only [weight_sq, one_mul]

end PoincareConjecture.RoundCylinderReflection
