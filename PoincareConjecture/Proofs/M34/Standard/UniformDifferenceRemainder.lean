import PoincareConjecture.Proofs.M34.Standard.UniformDifferenceFlux











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set
open scoped BigOperators

namespace PoincareConjecture.M34.DifferenceEnergy



noncomputable def curvatureDifferenceRemainder {n dS : ℕ}
    (qS : FS n ≃L[ℝ] EuclideanSpace ℝ (Fin dS))
    (I0 I1 : Inverse n) (gamma : Gamma n) (R1 : Raw n) (kp vp : Flux n)
    (d : Fin dS × Fin n → ℝ) (H : FH n) (A : FA n) (S : FS n) : Fin dS → ℝ :=
  curvatureContraction qS
    (divergenceAction gamma (principalFlux I0 qS d +
      curvatureDifferenceFlux I0 I1 gamma R1 kp H A S) + connectionRemainder vp A)




theorem exists_uniform_curvatureDifferenceRemainder_bound
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {n dH dA dS : ℕ}
    (qH : FH n ≃L[ℝ] EuclideanSpace ℝ (Fin dH))
    (qA : FA n ≃L[ℝ] EuclideanSpace ℝ (Fin dA))
    (qS : FS n ≃L[ℝ] EuclideanSpace ℝ (Fin dS))
    {I0 I1 : X → Inverse n} {gamma : X → Gamma n} {R1 : X → Raw n}
    {kp vp : X → Flux n}
    (hI0 : ContinuousOn I0 K) (hI1 : ContinuousOn I1 K)
    (hgamma : ∀ i j l, ContinuousOn (fun p => gamma p i j l) K)
    (hR1 : ∀ l j k m, ContinuousOn (fun p => R1 p l j k m) K)
    (hkp : ∀ d l j k m, ContinuousOn (fun p => kp p d l j k m) K)
    (hvp : ∀ i l j k m, ContinuousOn (fun p => vp p i l j k m) K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K, ∀ d : Fin dS × Fin n → ℝ,
      ∀ H : FH n, ∀ A : FA n, ∀ S : FS n, ∀ ε : ℝ, 0 < ε →
        (∑ alpha : Fin dS, 2 * qS S alpha *
          curvatureDifferenceRemainder qS (I0 p) (I1 p) (gamma p) (R1 p)
            (kp p) (vp p) d H A S alpha) ≤
          ε * (∑ beta, d beta ^ 2) + (C / ε + C) *
            ((∑ j, qH H j ^ 2) + (∑ j, qA A j ^ 2) + (∑ j, qS S j ^ 2)) := by
  classical
  let rd : X → Flux n →ₗ[ℝ] (Fin dS → ℝ) :=
    fun p => (curvatureContraction qS).comp (divergenceAction (gamma p))
  let LD : X → (Fin dS × Fin n → ℝ) →ₗ[ℝ] (Fin dS → ℝ) :=
    fun p => (rd p).comp (principalFlux (I0 p) qS)
  let LH : X → FH n →ₗ[ℝ] (Fin dS → ℝ) :=
    fun p => (rd p).comp (metricFlux (I0 p) (I1 p) (kp p))
  let LA : X → FA n →ₗ[ℝ] (Fin dS → ℝ) := fun p =>
    (rd p).comp (connectionFlux (I0 p) (R1 p)) +
      (curvatureContraction qS).comp (connectionRemainder (vp p))
  let LS : X → FS n →ₗ[ℝ] (Fin dS → ℝ) :=
    fun p => (rd p).comp (curvatureFlux (I0 p) (gamma p))
  obtain ⟨CL, hCL, hlow⟩ := exists_compact_three_linear_coordinate_bound hK qH qA qS LH LA LS
    (fun H alpha => continuousOn_curvatureContraction qS
      (fun l j k m => continuousOn_divergenceAction hgamma
        (fun i l j k m => continuousOn_metricFlux hI0 hI1 hkp H i l j k m) l j k m) alpha)
    (fun A alpha => (continuousOn_curvatureContraction qS
      (fun l j k m => continuousOn_divergenceAction hgamma
        (fun i l j k m => continuousOn_connectionFlux hI0 hR1 A i l j k m) l j k m)
          alpha).add (continuousOn_curvatureContraction qS
            (fun l j k m => continuousOn_connectionRemainder hvp A l j k m) alpha))
    (fun S alpha => continuousOn_curvatureContraction qS
      (fun l j k m => continuousOn_divergenceAction hgamma
        (fun i l j k m => continuousOn_curvatureFlux hI0 hgamma S i l j k m) l j k m) alpha)
  obtain ⟨CD, hCD, hderiv⟩ := exists_compact_finite_linear_coordinate_bound hK LD
    (fun d alpha => continuousOn_curvatureContraction qS
      (fun l j k m => continuousOn_divergenceAction hgamma
        (fun i l j k m => continuousOn_principalFlux hI0 qS d i l j k m) l j k m) alpha)
  let C := CD + CL + 1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, fun p hp d H A S ε hε => ?_⟩
  let density := (∑ j, qH H j ^ 2) + (∑ j, qA A j ^ 2) + (∑ j, qS S j ^ 2)
  have hden : 0 ≤ density := by dsimp [density]; positivity
  have hS : (∑ j, qS S j ^ 2) ≤ density := by
    dsimp only [density]
    have hH : 0 ≤ ∑ j, qH H j ^ 2 := by positivity
    have hA : 0 ≤ ∑ j, qA A j ^ 2 := by positivity
    linarith
  have hd := (hderiv p hp d).2 ε hε (fun alpha => qS S alpha)
  have hl := (hlow p hp H A S).2 1 (by norm_num) (fun alpha => qS S alpha)
  simp only [one_mul, div_one] at hl
  have hCDle : CD ≤ C := by dsimp [C]; linarith
  have hCLle : CL + 1 ≤ C := by dsimp [C]; linarith
  have hdb : CD / ε * (∑ j, qS S j ^ 2) ≤ C / ε * density :=
    mul_le_mul (div_le_div_of_nonneg_right hCDle hε.le) hS
      (by positivity) (div_nonneg hC hε.le)
  have hlb : density + CL * (∑ j, qS S j ^ 2) ≤ C * density := by
    have h₁ := mul_le_mul_of_nonneg_left hS hCL
    have h₂ := mul_le_mul_of_nonneg_right hCLle hden
    nlinarith only [h₁, h₂]
  have hvalue (alpha : Fin dS) :
      curvatureDifferenceRemainder qS (I0 p) (I1 p) (gamma p) (R1 p)
        (kp p) (vp p) d H A S alpha =
        LD p d alpha + (LH p H alpha + LA p A alpha + LS p S alpha) := by
    simp only [curvatureDifferenceRemainder, curvatureDifferenceFlux_eq, LD, LH, LA, LS,
      rd, LinearMap.comp_apply, LinearMap.add_apply, Pi.add_apply, map_add]
    ring
  have hrate :
      (∑ alpha : Fin dS, 2 * qS S alpha *
        curvatureDifferenceRemainder qS (I0 p) (I1 p) (gamma p) (R1 p)
          (kp p) (vp p) d H A S alpha) =
        (∑ alpha, 2 * qS S alpha * LD p d alpha) +
          (∑ alpha, 2 * qS S alpha * (LH p H alpha + LA p A alpha + LS p S alpha)) := by
    simp only [hvalue, mul_add, Finset.sum_add_distrib]
  rw [hrate]
  change _ ≤ ε * (∑ beta, d beta ^ 2) + (C / ε + C) * density
  nlinarith only [hd, hl, hdb, hlb]

end PoincareConjecture.M34.DifferenceEnergy
