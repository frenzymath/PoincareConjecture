import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Event.LimitJets
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Composition

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Analysis.Calculus

variable {d : ℕ}

def bilinearBasisEvaluation (i j : Fin d) :
    (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.basisFun (Fin d) ℝ j)).comp
    (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
      (EuclideanSpace.basisFun (Fin d) ℝ i))

theorem bilinear_eq_of_basis
    {A B : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ}
    (h : ∀ i j, bilinearBasisEvaluation i j A = bilinearBasisEvaluation i j B) :
    A = B := by
  have houter : A.toLinearMap = B.toLinearMap :=
    (EuclideanSpace.basisFun (Fin d) ℝ).toBasis.ext fun i => by
      have hinner : (A (EuclideanSpace.basisFun (Fin d) ℝ i)).toLinearMap =
          (B (EuclideanSpace.basisFun (Fin d) ℝ i)).toLinearMap :=
        (EuclideanSpace.basisFun (Fin d) ℝ).toBasis.ext fun j => h i j
      exact ContinuousLinearMap.ext fun v => congrArg (fun L => L v) hinner
  exact ContinuousLinearMap.ext fun v => congrArg (fun L => L v) houter

def linearJetEvaluation {E B F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (k : ℕ) (e : B →L[ℝ] F) :
    (ContinuousMultilinearMap ℝ (fun _ : Fin k => E) B) →L[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin k => E) F :=
  ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin k => E) B F e

private theorem finiteDimensional_jets {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] (k : ℕ) :
    FiniteDimensional ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin k => E) F) := by
  induction k with
  | zero =>
      exact FiniteDimensional.of_injective
        (continuousMultilinearCurryFin0 ℝ E F).toLinearMap
        (continuousMultilinearCurryFin0 ℝ E F).injective
  | succ k ih =>
      let := ih
      exact FiniteDimensional.of_injective
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => E) F).toLinearMap
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => E) F).injective

theorem tendstoUniformlyOn_bilinear_jets_of_components
    {α : Type*} {l : Filter α} {K : Set (EuclideanSpace ℝ (Fin d))}
    {B : α → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ]
      EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ}
    {B₀ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ]
      EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ}
    (hB : ∀ t x, x ∈ K → ContDiffAt ℝ ∞ (B t) x)
    (hB₀ : ∀ x ∈ K, ContDiffAt ℝ ∞ B₀ x) (k : ℕ)
    (h : ∀ i j, TendstoUniformlyOn
      (fun t => iteratedFDeriv ℝ k (fun x => bilinearBasisEvaluation i j (B t x)))
      (iteratedFDeriv ℝ k (fun x => bilinearBasisEvaluation i j (B₀ x))) l K) :
    TendstoUniformlyOn (fun t => iteratedFDeriv ℝ k (B t))
      (iteratedFDeriv ℝ k B₀) l K := by
  let := finiteDimensional_jets (E := EuclideanSpace ℝ (Fin d)) (F := ℝ) k
  apply tendstoUniformlyOn_of_finite_linear_evaluations
    (fun ij : Fin d × Fin d => linearJetEvaluation
      (E := EuclideanSpace ℝ (Fin d))
      (B := EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
      (F := ℝ) k (bilinearBasisEvaluation ij.1 ij.2))
  · intro A B hAB
    apply ContinuousMultilinearMap.ext
    intro v
    apply bilinear_eq_of_basis
    intro i j
    exact congrArg (fun L => L v) (hAB (i, j))
  · rintro ⟨i, j⟩
    apply ((h i j).congr (Eventually.of_forall fun t x hx => ?_)).congr_right
    · intro x hx
      exact (bilinearBasisEvaluation i j).iteratedFDeriv_comp_left
        (hB₀ x hx) (by exact_mod_cast le_top)
    · exact (bilinearBasisEvaluation i j).iteratedFDeriv_comp_left
        (hB t x hx) (by exact_mod_cast le_top)

end Poincare.Analysis.Calculus
