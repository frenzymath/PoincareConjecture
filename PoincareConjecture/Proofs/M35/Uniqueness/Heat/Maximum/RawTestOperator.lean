import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Maximum.FieldEmbedding
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Maximum.FieldEntropy
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawLowerBounds
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawCompactHeat









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set
open scoped SchwartzMap LineDeriv ContDiff

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "e" => fun i : Fin n => EuclideanSpace.single i (1 : ℝ)

theorem schwartzField_fderiv_component (f : Fin n → 𝓢(V, ℝ)) (x v : V) (j : Fin n) :
    (fderiv ℝ (schwartzField f) x v) j = fderiv ℝ (f j) x v := by
  change ((∂_{v} (schwartzField f)) x) j = _
  rw [schwartzField_partial, schwartzField_apply]
  rfl

private theorem cutoff_supported_mul {K : Set V} (η : V → ℝ)
    (hηK : ∀ x ∈ K, η x = 1) (a : V → ℝ) (f : supportedTests K) (x : V) :
    (η x * a x) * (f : 𝓢(V, ℝ)) x = a x * (f : 𝓢(V, ℝ)) x := by
  by_cases hx : x ∈ K
  · rw [hηK x hx, one_mul]
  · rw [f.property x hx, mul_zero, mul_zero]

theorem raw_principalTestLaplacian_apply {K : Set V} (hK : IsClosed K)
    (g : RiemannianMetric n V) (η : 𝓢(V, ℝ)) (hη : HasCompactSupport η)
    (hηK : ∀ x ∈ K, η x = 1) (f : supportedTests K) (x : V) :
    (principalTestLaplacian hK (rawCutoffPrincipalCoefficient g η hη) f : 𝓢(V, ℝ)) x =
      ∑ i, ∑ j, fderiv ℝ (fun y => (rawCoordinateGram g y)⁻¹ i j *
        fderiv ℝ (f : 𝓢(V, ℝ)) y (e j)) x (e i) := by
  simp only [principalTestLaplacian, LinearMap.sum_apply, LinearMap.comp_apply,
    Submodule.coe_sum, sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change fderiv ℝ (fun y =>
    (rawCutoffPrincipalCoefficient g η hη i j) y *
      fderiv ℝ (f : 𝓢(V, ℝ)) y (e j)) x (e i) = _
  have he : (fun y => (rawCutoffPrincipalCoefficient g η hη i j) y *
      fderiv ℝ (f : 𝓢(V, ℝ)) y (e j)) =
      (fun y => (rawCoordinateGram g y)⁻¹ i j * fderiv ℝ (f : 𝓢(V, ℝ)) y (e j)) := by
    funext y
    exact cutoff_supported_mul η hηK (fun y => (rawCoordinateGram g y)⁻¹ i j)
      (testPartial hK j f) y
  rw [he]

theorem raw_lowerTestOperator_apply {K : Set V} (hK : IsClosed K)
    {g : RiemannianMetric n V} (D : LeviCivitaData g)
    (η : 𝓢(V, ℝ)) (hη : HasCompactSupport η) (hηK : ∀ x ∈ K, η x = 1)
    (f : Fin n → supportedTests K) (x : V) (k : Fin n) :
    ((∑ j, lowerTestOperator hK (rawCutoffFirstComponent D η hη k j)
      (rawCutoffZeroComponent D η hη k j) (f j)) : 𝓢(V, ℝ)) x =
      rawDivergenceFirstOrder D x (fderiv ℝ (schwartzField (fun j => (f j : 𝓢(V, ℝ)))) x) k +
        rawZeroOrderCoefficient D x (schwartzField (fun j => (f j : 𝓢(V, ℝ))) x) k := by
  simp only [lowerTestOperator, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.comp_apply, Submodule.coe_sum, Submodule.coe_add,
    sum_apply, add_apply, Finset.sum_add_distrib]
  rw [rawDivergenceFirstOrder_components, rawZeroOrderCoefficient_components]
  congr 1
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [schwartzField_fderiv_component]
    exact cutoff_supported_mul η hηK (rawFirstComponent D k j i) (testPartial hK i (f j)) x
  · apply Finset.sum_congr rfl
    intro j _
    rw [schwartzField_apply]
    exact cutoff_supported_mul η hηK (rawZeroComponent D k j) (f j) x

theorem raw_vectorTestGenerator_geometric {K : Set V} (hK : IsClosed K)
    {g : RiemannianMetric n V} (D : LeviCivitaData g)
    (η : 𝓢(V, ℝ)) (hη : HasCompactSupport η) (hηK : ∀ x ∈ K, η x = 1)
    (f : Fin n → supportedTests K) (x : V) (k : Fin n) :
    (vectorTestGenerator hK (rawCutoffPrincipalCoefficient g η hη)
      (rawCutoffFirstComponent D η hη) (rawCutoffZeroComponent D η hη) f k : 𝓢(V, ℝ)) x =
      (fieldTraceHessian D (schwartzField (fun j => (f j : 𝓢(V, ℝ)))) x +
        rawRicciLinear D x (schwartzField (fun j => (f j : 𝓢(V, ℝ))) x)) k := by
  let X : 𝓢(V, V) := schwartzField (fun j => (f j : 𝓢(V, ℝ)))
  have hgeo := congrArg (fun z : V => z k) (raw_vector_heat_divergence_operator D X.smooth' x)
  change (fieldTraceHessian D X x + rawRicciLinear D x (X x)) k = _ at hgeo
  change _ = (fieldTraceHessian D X x + rawRicciLinear D x (X x)) k
  rw [hgeo]
  simp only [vectorTestGenerator, Submodule.coe_add, add_apply, Submodule.coe_sum]
  rw [raw_principalTestLaplacian_apply hK g η hη hηK (f k) x,
    raw_lowerTestOperator_apply hK D η hη hηK f x k]
  simp only [PiLp.add_apply, WithLp.ofLp_sum, Finset.sum_apply]
  have he (i j : Fin n) :
      (fderiv ℝ (fun y => (rawCoordinateGram g y)⁻¹ i j • fderiv ℝ X y (e j)) x (e i)) k =
        fderiv ℝ (fun y => (rawCoordinateGram g y)⁻¹ i j *
          fderiv ℝ (f k : 𝓢(V, ℝ)) y (e j)) x (e i) := by
    have hA : ContDiff ℝ ∞ (fun y => (rawCoordinateGram g y)⁻¹ i j • fderiv ℝ X y (e j)) :=
      (raw_inverseGram_entry_contDiff g i j).smul
        ((X.smooth'.fderiv_right (by simp)).clm_apply contDiff_const)
    have hp := (EuclideanSpace.proj k).hasFDerivAt.comp x
      (hA.differentiable (by simp) x).hasFDerivAt
    have hf : (fun y => (EuclideanSpace.proj k)
        ((rawCoordinateGram g y)⁻¹ i j • fderiv ℝ X y (e j))) =
        fun y => (rawCoordinateGram g y)⁻¹ i j * fderiv ℝ (f k : 𝓢(V, ℝ)) y (e j) := by
      funext y
      change (rawCoordinateGram g y)⁻¹ i j * (fderiv ℝ X y (e j)) k = _
      rw [schwartzField_fderiv_component]
    simp only [Function.comp_def] at hp
    rw [hf] at hp
    exact (congrArg (fun A : V →L[ℝ] ℝ => A (e i)) hp.fderiv).symm
  have hsum := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun i _ => Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
      (fun j _ => he i j))
  convert! congrArg (fun a : ℝ => a + rawDivergenceFirstOrder D x (fderiv ℝ X x) k +
    rawZeroOrderCoefficient D x (X x) k) hsum.symm using 1
  ring

end PoincareConjecture.M35.Uniqueness.Heat
