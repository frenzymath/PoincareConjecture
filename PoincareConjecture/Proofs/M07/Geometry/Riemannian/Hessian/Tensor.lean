import PoincareConjecture.Proofs.M07.Geometry.Riemannian.ScalarOperators
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.ScalarOperators.Gradient
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.Calculus
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

noncomputable def differentialEvaluation (f : M → ℝ) : CovariantTensorEvaluation n M 1 :=
  fun x v ↦ mvfderiv (𝓡 n) f x (v 0)

lemma differentialEvaluation_isSmooth
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) :
    IsSmoothCovariantTensor (differentialEvaluation (n := n) f) := by
  constructor
  · intro x
    exact ⟨MultilinearMap.ofSubsingleton ℝ (TangentSpace (𝓡 n) x) ℝ
      (0 : Fin 1) (mvfderiv (𝓡 n) f x).toLinearMap, fun _ ↦ rfl⟩
  · intro U hU X hX
    have htan := hf.contMDiff_tangentMap (m := ∞) (by simp)
    have hcomp := htan.comp_contMDiffOn (hX 0)
    have hsnd := (contMDiff_snd_tangentBundle_modelSpace ℝ 𝓘(ℝ, ℝ) (n := ∞)).comp_contMDiffOn
      hcomp
    exact hsnd

namespace LeviCivitaData

variable {g : RiemannianMetric n M}

lemma hessian_eq_covariantTensorDerivative
    (D : LeviCivitaData g) (f : M → ℝ) (x : M)
    (u v : TangentSpace (𝓡 n) x) :
    D.hessian f x u v = D.covariantTensorDerivative (differentialEvaluation f) x ![u, v] := by
  simp [hessian, hessianOnFields, covariantTensorDerivative, differentialEvaluation]

lemma hessian_isSmoothCovariantTensor
    (D : LeviCivitaData g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) :
    IsSmoothCovariantTensor (k := 2) (fun x v ↦ D.hessian f x (v 0) (v 1)) := by
  constructor
  · intro x
    let A : MultilinearMap ℝ (fun _ : Fin 2 => TangentSpace (𝓡 n) x) ℝ :=
      { toFun := fun v => g.inner x (D.connection (D.gradient f) x (v 0)) (v 1)
        map_update_add' := by
          intro _ v i a b
          fin_cases i <;> simp [map_add]
        map_update_smul' := by
          intro _ v i c a
          fin_cases i <;> simp }
    exact ⟨A, fun v => D.hessian_eq_inner_connection_gradient (hf x) _ _⟩
  · intro U hU X hX
    have hgrad := D.contMDiff_gradient hf
    have hconnection := D.smooth.contMDiff.contMDiff
      (show ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        (∞ + 1) (T% (D.gradient f)) Set.univ from by simpa using hgrad.contMDiffOn)
    have hc := (contMDiffOn_univ.mp hconnection).contMDiffOn.clm_bundle_apply (hX 0)
    have hi := (g.contMDiff.contMDiffOn.clm_bundle_apply hc).clm_bundle_apply (hX 1)
    intro x hx
    have hscalar := (Bundle.contMDiffAt_totalSpace.mp
      ((hi x hx).contMDiffAt (hU.mem_nhds hx))).2
    simpa [hessian_eq_inner_connection_gradient D (hf _)] using hscalar.contMDiffWithinAt

end LeviCivitaData
end PoincareConjecture
