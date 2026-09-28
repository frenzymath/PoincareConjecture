import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Tensor.Spacetime
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Regularity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Tensors


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace Poincare.RicciFlow.Harnack

open PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

lemma contMDiffAt_covariantRicciDerivative_fields
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    {t : ℝ} (ht : t ∈ interior J) {x : M}
    {X : Fin 3 → (y : M) → TangentSpace (𝓡 n) y}
    (hX : ∀ i, ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (T% (X i)) x) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => (F.connection p.1).covariantTensorDerivative
        (F.connection p.1).ricciEvaluation p.2 (fun i => X i p.2)) (t, x) := by
  apply F.contMDiffAt_covariantTensorDerivative_fields ht
    (fun s => (hC.tensor_calculus n M (F.metric s) (F.connection s)).2.1) _ hX
  intro Y hY
  exact F.contMDiffAt_ricci_fields ht (hY 0) (hY 1)

lemma contMDiffAt_hamiltonP_fields
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    {t : ℝ} (ht : t ∈ interior J) {x : M}
    {X : Fin 3 → (y : M) → TangentSpace (𝓡 n) y}
    (hX : ∀ i, ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (T% (X i)) x) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => hamiltonP (F.connection p.1) p.2
        (X 0 p.2) (X 1 p.2) (X 2 p.2)) (t, x) := by
  have ha := contMDiffAt_covariantRicciDerivative_fields hC F ht hX
  have hb := contMDiffAt_covariantRicciDerivative_fields hC F ht
    (X := fun i => X (Equiv.swap 0 1 i)) (fun i => hX _)
  have heq (p : ℝ × M) :
      (fun i : Fin 3 => X i p.2) = ![X 0 p.2, X 1 p.2, X 2 p.2] := by
    ext i; fin_cases i <;> rfl
  have hswap (p : ℝ × M) :
      (fun i : Fin 3 => X (Equiv.swap 0 1 i) p.2) = ![X 1 p.2, X 0 p.2, X 2 p.2] := by
    ext i; fin_cases i <;> simp [Equiv.swap_apply_def]
  simpa only [heq, hswap, hamiltonP] using ha.sub hb

lemma contMDiffAt_covariantHamiltonP_fields
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    {t : ℝ} (ht : t ∈ interior J) {x : M}
    {X : Fin 4 → (y : M) → TangentSpace (𝓡 n) y}
    (hX : ∀ i, ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (T% (X i)) x) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => (F.connection p.1).covariantTensorDerivative
        (fun y z => hamiltonP (F.connection p.1) y (z 0) (z 1) (z 2)) p.2
        (fun i => X i p.2)) (t, x) := by
  apply F.contMDiffAt_covariantTensorDerivative_fields ht
    (fun s => hamiltonP_isSmoothCovariantTensor (F.connection s)
      (hC.tensor_calculus n M (F.metric s) (F.connection s))) _ hX
  exact fun Y hY => contMDiffAt_hamiltonP_fields hC F ht hY

end Poincare.RicciFlow.Harnack
