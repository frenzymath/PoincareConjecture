import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff

namespace PoincareConjecture.Proofs.M09

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

noncomputable def bilinearOfMultilinear (A : MultilinearMap ℝ (fun _ : Fin 2 ↦ V) ℝ) :
    V →L[ℝ] V →L[ℝ] ℝ :=
  let L : V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
    (MultilinearMap.ofSubsingletonₗ ℝ ℝ V ℝ (0 : Fin 1)).symm.toLinearMap.comp A.curryLeft
  ((LinearMap.toContinuousLinearMap : (V →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (V →L[ℝ] ℝ)).toLinearMap.comp
    L).toContinuousLinearMap

theorem bilinearOfMultilinear_apply (A : MultilinearMap ℝ (fun _ : Fin 2 ↦ V) ℝ)
    (v w : V) : bilinearOfMultilinear A v w = A ![v, w] := by
  change A (Fin.cons v (fun _ : Fin 1 ↦ w)) = A ![v, w]
  congr 1
  funext i
  fin_cases i <;> rfl

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

theorem contMDiffOn_clm_iff
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {k : WithTop ℕ∞} {f : M → V →L[ℝ] W} {U : Set M} :
    ContMDiffOn (𝓡 n) (𝓘(ℝ, V →L[ℝ] W)) k f U ↔
      ∀ v, ContMDiffOn (𝓡 n) (𝓘(ℝ, W)) k (fun q ↦ f q v) U := by
  constructor
  · intro h v
    exact h.clm_apply contMDiffOn_const
  · intro h
    let d := Module.finrank ℝ V
    have hd : d = Module.finrank ℝ (Fin d → ℝ) := (Module.finrank_fin_fun ℝ).symm
    let e₁ : V ≃L[ℝ] (Fin d → ℝ) := ContinuousLinearEquiv.ofFinrankEq hd
    let e₂ := (e₁.arrowCongr (ContinuousLinearEquiv.refl ℝ W)).trans
      (ContinuousLinearEquiv.piRing (Fin d))
    rw [← Function.id_comp f, ← e₂.symm_comp_self]
    exact e₂.symm.toContinuousLinearMap.contMDiff.comp_contMDiffOn
      (contMDiffOn_pi_space.mpr fun i ↦ h _)

theorem contMDiffOn_bilinear_iff {k : WithTop ℕ∞}
    {f : M → V →L[ℝ] V →L[ℝ] ℝ} {U : Set M} :
    ContMDiffOn (𝓡 n) (𝓘(ℝ, V →L[ℝ] V →L[ℝ] ℝ)) k f U ↔
      ∀ v w, ContMDiffOn (𝓡 n) (𝓘(ℝ, ℝ)) k (fun q ↦ f q v w) U := by
  rw [contMDiffOn_clm_iff]
  simp_rw [contMDiffOn_clm_iff]

end PoincareConjecture.Proofs.M09
