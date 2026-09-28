import PoincareConjecture.Proofs.M34.Standard.DifferenceFluxContinuity
import PoincareConjecture.Proofs.M34.Mathlib.FiniteCoordinateBounds











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set
open scoped BigOperators

namespace PoincareConjecture.M34.DifferenceEnergy




theorem exists_uniform_curvatureDifferenceFlux_bound
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    {n dH dA dS : ℕ}
    (qH : FH n ≃L[ℝ] EuclideanSpace ℝ (Fin dH))
    (qA : FA n ≃L[ℝ] EuclideanSpace ℝ (Fin dA))
    (qS : FS n ≃L[ℝ] EuclideanSpace ℝ (Fin dS))
    {I0 I1 : X → Inverse n} {gamma : X → Gamma n} {R1 : X → Raw n} {kp : X → Flux n}
    (hI0 : ContinuousOn I0 K) (hI1 : ContinuousOn I1 K)
    (hgamma : ∀ i j l, ContinuousOn (fun p => gamma p i j l) K)
    (hR1 : ∀ l j k m, ContinuousOn (fun p => R1 p l j k m) K)
    (hkp : ∀ d l j k m, ContinuousOn (fun p => kp p d l j k m) K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K, ∀ H : FH n, ∀ A : FA n, ∀ S : FS n,
      (∑ alpha : Fin dS, ∑ i : Fin n,
        curvatureContraction qS
          (curvatureDifferenceFlux (I0 p) (I1 p) (gamma p) (R1 p) (kp p) H A S i) alpha ^ 2) ≤
        C * ((∑ j, qH H j ^ 2) + (∑ j, qA A j ^ 2) + (∑ j, qS S j ^ 2)) := by
  classical
  let con : Flux n →ₗ[ℝ] (Fin dS × Fin n → ℝ) :=
    LinearMap.pi (fun alpha => ((LinearMap.proj alpha.1).comp (curvatureContraction qS)).comp
      (LinearMap.proj alpha.2))
  let LH : X → FH n →ₗ[ℝ] (Fin dS × Fin n → ℝ) :=
    fun p => con.comp (metricFlux (I0 p) (I1 p) (kp p))
  let LA : X → FA n →ₗ[ℝ] (Fin dS × Fin n → ℝ) :=
    fun p => con.comp (connectionFlux (I0 p) (R1 p))
  let LS : X → FS n →ₗ[ℝ] (Fin dS × Fin n → ℝ) :=
    fun p => con.comp (curvatureFlux (I0 p) (gamma p))
  obtain ⟨C, hC, hbound⟩ := exists_compact_three_linear_coordinate_bound hK qH qA qS LH LA LS
    (fun H alpha => continuousOn_curvatureContraction qS
      (fun l j k m => continuousOn_metricFlux hI0 hI1 hkp H alpha.2 l j k m) alpha.1)
    (fun A alpha => continuousOn_curvatureContraction qS
      (fun l j k m => continuousOn_connectionFlux hI0 hR1 A alpha.2 l j k m) alpha.1)
    (fun S alpha => continuousOn_curvatureContraction qS
      (fun l j k m => continuousOn_curvatureFlux hI0 hgamma S alpha.2 l j k m) alpha.1)
  refine ⟨C, hC, fun p hp H A S => ?_⟩
  have h := (hbound p hp H A S).1
  have hvalue (alpha : Fin dS × Fin n) : LH p H alpha + LA p A alpha + LS p S alpha =
      curvatureContraction qS
        (curvatureDifferenceFlux (I0 p) (I1 p) (gamma p) (R1 p) (kp p) H A S alpha.2)
          alpha.1 := by
    rw [curvatureDifferenceFlux_eq]
    simp only [LH, LA, LS, con, LinearMap.comp_apply, LinearMap.pi_apply,
      LinearMap.proj_apply, Pi.add_apply, map_add]
  simp_rw [hvalue] at h
  simpa only [Fintype.sum_prod_type] using h

end PoincareConjecture.M34.DifferenceEnergy
