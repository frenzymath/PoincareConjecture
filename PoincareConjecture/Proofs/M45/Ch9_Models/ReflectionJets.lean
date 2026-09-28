import PoincareConjecture.Proofs.M45.Ch9_Models.ReflectionBasics









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff BigOperators

namespace PoincareConjecture.M45

open M36 M44

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "V" => RoundCylinderCoordinates

def cylinderSlotSign {r : ℕ} (a : Fin r → Fin 3) : ℝ :=
  ∏ i, cylinderReflectionSign (a i)

@[simp] theorem cylinderSlotSign_sq {r : ℕ} (a : Fin r → Fin 3) :
    cylinderSlotSign a ^ 2 = 1 := by
  simp only [cylinderSlotSign, ← Finset.prod_pow, cylinderReflectionSign_sq,
    Finset.prod_const_one]

theorem cylinderSlotSign_succ {r : ℕ} (a : Fin (r + 1) → Fin 3) :
    cylinderSlotSign a = cylinderReflectionSign (a 0) *
      cylinderSlotSign (fun i => a i.succ) :=
  Fin.prod_univ_succ _

theorem cylinderSlotSign_update {r : ℕ} (a : Fin r → Fin 3) (i : Fin r) (j : Fin 3) :
    cylinderSlotSign (Function.update a i j) =
      cylinderReflectionSign (a i) * cylinderReflectionSign j * cylinderSlotSign a := by
  classical
  have hu : (fun k => cylinderReflectionSign (Function.update a i j k)) =
      Function.update (fun k => cylinderReflectionSign (a k)) i
        (cylinderReflectionSign j) := by
    funext k
    by_cases h : k = i <;> simp [h]
  unfold cylinderSlotSign
  rw [hu, Finset.prod_update_of_mem (Finset.mem_univ i)]
  rw [← Finset.mul_prod_erase Finset.univ (fun k => cylinderReflectionSign (a k))
    (Finset.mem_univ i)]
  rw [Finset.sdiff_singleton_eq_erase]
  symm
  calc
    _ = cylinderReflectionSign (a i) ^ 2 *
        (cylinderReflectionSign j * ∏ x ∈ Finset.univ.erase i,
          cylinderReflectionSign (a x)) := by ring
    _ = _ := by rw [cylinderReflectionSign_sq, one_mul]

theorem cylinderReflection_fderiv (c : ℝ) (f : V → ℝ) (p : V) (a : Fin 3) :
    fderiv ℝ (fun q => c * f (cylinderCoordinateReflection q)) p
        (roundCylinderCoordinateBasis a) =
      c * cylinderReflectionSign a *
        fderiv ℝ f (cylinderCoordinateReflection p) (roundCylinderCoordinateBasis a) := by
  change fderiv ℝ (c • (f ∘ cylinderCoordinateReflection)) p
    (roundCylinderCoordinateBasis a) = _
  rw [fderiv_const_smul_field, Pi.smul_apply,
    cylinderCoordinateReflection.comp_right_fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
  change c * fderiv ℝ f (cylinderCoordinateReflection p)
    (cylinderCoordinateReflection (roundCylinderCoordinateBasis a)) = _
  rw [cylinderCoordinateReflection_basis, map_smul]
  simp only [smul_eq_mul]
  ring

theorem cylinderReflection_tensorDerivative {t : ℝ} (ht : t < 1)
    (theta : UnitTwoSphere) {r : ℕ} (T : V → (Fin r → Fin 3) → ℝ)
    (p : V) (a : Fin (r + 1) → Fin 3) :
    roundCylinderTensorDerivative t (chartAt E₂ theta)
        (fun q b => cylinderSlotSign b * T (cylinderCoordinateReflection q) b) p a =
      cylinderSlotSign a * roundCylinderTensorDerivative t (chartAt E₂ theta) T
        (cylinderCoordinateReflection p) a := by
  unfold roundCylinderTensorDerivative
  dsimp only
  rw [cylinderReflection_fderiv (cylinderSlotSign (fun i => a i.succ))
    (fun q => T q (fun i => a i.succ)), cylinderSlotSign_succ, mul_sub]
  congr 1
  · ring
  · simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [cylinderReflection_christoffel ht, cylinderSlotSign_update]
    calc
      _ = (cylinderReflectionSign j ^ 2 * cylinderReflectionSign (a i.succ) ^ 2) *
          (cylinderReflectionSign (a 0) * cylinderSlotSign (fun k => a k.succ) *
            (roundCylinderChristoffel t (chartAt E₂ theta)
                (cylinderCoordinateReflection p) j (a 0) (a i.succ) *
              T (cylinderCoordinateReflection p)
                (Function.update (fun k => a k.succ) i j))) := by ring
      _ = _ := by rw [cylinderReflectionSign_sq, cylinderReflectionSign_sq, one_mul, one_mul]

theorem cylinderReflectedTensor_iteratedDerivative {t : ℝ} (ht : t < 1)
    (B : RoundCylinderTwoTensor) (hB : ∀ z, IsBilinearMap ℝ (B z))
    (theta : UnitTwoSphere) (k : ℕ) :
    roundCylinderIteratedDerivative t (chartAt E₂ theta) (cylinderReflectedTensor B) k =
      fun p a => cylinderSlotSign a *
        roundCylinderIteratedDerivative t (chartAt E₂ theta) B k
          (cylinderCoordinateReflection p) a := by
  induction k with
  | zero =>
      funext p a
      simp only [roundCylinderIteratedDerivative, cylinderReflectedTensor_coefficient B hB,
        cylinderSlotSign]
      rw [Fin.prod_univ_two (fun i : Fin 2 => cylinderReflectionSign (a i))]
      rw [cylinderReflection_gram t theta p]
      ring
  | succ k ih =>
      simp only [roundCylinderIteratedDerivative, ih]
      funext p a
      exact cylinderReflection_tensorDerivative ht theta _ p a

theorem cylinderReflection_tensorNormSquared {t : ℝ} (ht : t < 1) {r : ℕ}
    (theta : UnitTwoSphere) (s : ℝ) (T : (Fin r → Fin 3) → ℝ) :
    roundCylinderTensorNormSquared t (chartAt E₂ theta)
        (chartAt E₂ theta theta, s) (fun a => cylinderSlotSign a * T a) =
      roundCylinderTensorNormSquared t (chartAt E₂ theta)
        (chartAt E₂ theta theta, -s) T := by
  rw [evolving_roundCylinderTensorNormSquared_center ht,
    evolving_roundCylinderTensorNormSquared_center ht]
  apply Finset.sum_congr rfl
  intro a _
  rw [mul_pow, cylinderSlotSign_sq, one_mul]

theorem cylinderReflectedTensor_jetError {t : ℝ} (ht : t < 1)
    (B : RoundCylinderTwoTensor) (hB : ∀ z, IsBilinearMap ℝ (B z))
    (k : ℕ) (z : RoundCylinderSpace) :
    roundCylinderJetErrorSquared t (cylinderReflectedTensor B) k z =
      roundCylinderJetErrorSquared t B k (cylinderAxialReflection z) := by
  unfold roundCylinderJetErrorSquared
  dsimp only [cylinderAxialReflection]
  apply Finset.sum_congr rfl
  intro j _
  rw [cylinderReflectedTensor_iteratedDerivative ht B hB]
  exact cylinderReflection_tensorNormSquared ht z.1 z.2 _

theorem cylinderReflectedTensor_smooth {epsilon : ℝ} (B : RoundCylinderTwoTensor)
    (hB : ∀ z, IsBilinearMap ℝ (B z)) (hs : RoundCylinderTensorSmoothOn epsilon B) :
    RoundCylinderTensorSmoothOn epsilon (cylinderReflectedTensor B) := by
  intro theta a b
  simp only [cylinderReflectedTensor_coefficient B hB]
  apply contDiffOn_const.mul
  apply (hs theta a b).comp cylinderCoordinateReflection.contDiff.contDiffOn
  intro p hp
  exact ⟨hp.1, by simpa only [cylinderCoordinateReflection_apply] using
    (show -p.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ from ⟨by linarith [hp.2.2], by linarith [hp.2.1]⟩)⟩




theorem cylinderReflectedTensor_close {epsilon t : ℝ} (ht : t < 1)
    (B : RoundCylinderTwoTensor) (hB : ∀ z, IsBilinearMap ℝ (B z))
    (hclose : RoundCylinderClose epsilon t B) :
    RoundCylinderClose epsilon t (cylinderReflectedTensor B) := by
  refine ⟨cylinderReflectedTensor_smooth B hB hclose.1, ?_⟩
  obtain ⟨bound, hbound, hjets⟩ := hclose.2
  refine ⟨bound, hbound, fun z hz => ?_⟩
  rw [cylinderReflectedTensor_jetError ht B hB]
  apply hjets
  exact ⟨by dsimp [cylinderAxialReflection]; linarith [hz.2],
    by dsimp [cylinderAxialReflection]; linarith [hz.1]⟩

end PoincareConjecture.M45
