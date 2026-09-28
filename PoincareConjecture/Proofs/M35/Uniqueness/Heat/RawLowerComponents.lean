import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawDivergenceOperator
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.DirichletVectorLowerOrder









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set
open scoped SchwartzMap ContDiff

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "e" => fun i : Fin n => EuclideanSpace.single i (1 : ℝ)

def rawElementaryDerivative (i j : Fin n) : V →L[ℝ] V :=
  (EuclideanSpace.proj i).smulRight (e j)

theorem raw_linearMap_component_expansion (L : V →L[ℝ] V) :
    L = ∑ i, ∑ j, (L (e i)) j • rawElementaryDerivative i j := by
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.ext
  intro k
  ext l
  simp [rawElementaryDerivative, OrthonormalBasis.coe_toBasis,
    EuclideanSpace.basisFun_apply, EuclideanSpace.single, Pi.single_apply]

theorem raw_vector_component_expansion (v : V) : v = ∑ j, v j • e j := by
  ext k
  simp [EuclideanSpace.single, Pi.single_apply]

def rawFirstComponent {g : RiemannianMetric n V} (D : LeviCivitaData g)
    (k j i : Fin n) (x : V) : ℝ :=
  rawDivergenceFirstOrder D x (rawElementaryDerivative i j) k

def rawZeroComponent {g : RiemannianMetric n V} (D : LeviCivitaData g)
    (k j : Fin n) (x : V) : ℝ := rawZeroOrderCoefficient D x (e j) k

theorem rawDivergenceFirstOrder_components {g : RiemannianMetric n V}
    (D : LeviCivitaData g) (x : V) (L : V →L[ℝ] V) (k : Fin n) :
    rawDivergenceFirstOrder D x L k =
      ∑ i, ∑ j, rawFirstComponent D k j i x * (L (e i)) j := by
  conv_lhs => rw [raw_linearMap_component_expansion L]
  simp only [map_sum, map_smul, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

theorem rawZeroOrderCoefficient_components {g : RiemannianMetric n V}
    (D : LeviCivitaData g) (x v : V) (k : Fin n) :
    rawZeroOrderCoefficient D x v k = ∑ j, rawZeroComponent D k j x * v j := by
  conv_lhs => rw [raw_vector_component_expansion v]
  simp only [map_sum, map_smul, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

theorem rawFirstComponent_contDiff {g : RiemannianMetric n V}
    (D : LeviCivitaData g) (k j i : Fin n) : ContDiff ℝ ∞ (rawFirstComponent D k j i) := by
  exact (EuclideanSpace.proj k : V →L[ℝ] ℝ).contDiff.comp
    ((rawDivergenceFirstOrder_contDiff D).clm_apply
      (contDiff_const (c := rawElementaryDerivative i j)))

theorem rawZeroComponent_contDiff {g : RiemannianMetric n V}
    (D : LeviCivitaData g) (k j : Fin n) : ContDiff ℝ ∞ (rawZeroComponent D k j) := by
  exact (EuclideanSpace.proj k : V →L[ℝ] ℝ).contDiff.comp
    ((rawZeroOrderCoefficient_contDiff D).clm_apply (contDiff_const (c := e j)))

def rawCutoffFirstComponent {g : RiemannianMetric n V} (D : LeviCivitaData g)
    (η : 𝓢(V, ℝ)) (hη : HasCompactSupport η) (k j i : Fin n) : 𝓢(V, ℝ) :=
  EuclideanDerivativeNative.cutoffSchwartz η hη isOpen_univ (subset_univ _)
    (rawFirstComponent D k j i) (rawFirstComponent_contDiff D k j i).contDiffOn

def rawCutoffZeroComponent {g : RiemannianMetric n V} (D : LeviCivitaData g)
    (η : 𝓢(V, ℝ)) (hη : HasCompactSupport η) (k j : Fin n) : 𝓢(V, ℝ) :=
  EuclideanDerivativeNative.cutoffSchwartz η hη isOpen_univ (subset_univ _)
    (rawZeroComponent D k j) (rawZeroComponent_contDiff D k j).contDiffOn

@[simp] theorem rawCutoffFirstComponent_apply {g : RiemannianMetric n V}
    (D : LeviCivitaData g) (η : 𝓢(V, ℝ)) (hη : HasCompactSupport η)
    (k j i : Fin n) (x : V) : rawCutoffFirstComponent D η hη k j i x =
      η x * rawFirstComponent D k j i x := rfl

@[simp] theorem rawCutoffZeroComponent_apply {g : RiemannianMetric n V}
    (D : LeviCivitaData g) (η : 𝓢(V, ℝ)) (hη : HasCompactSupport η)
    (k j : Fin n) (x : V) : rawCutoffZeroComponent D η hη k j x =
      η x * rawZeroComponent D k j x := rfl

end PoincareConjecture.M35.Uniqueness.Heat
