import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Trace
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Positivity.Diagonal
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.MetricDuality

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators
open Set

universe u

namespace Poincare.RicciFlow.Harnack

open PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

def HamiltonBlockPos
    {T₀ T₁ : ℝ} (F : RicciFlow n M (Ioo T₀ T₁)) (t : ℝ) (x : M)
    (τ : ℝ) : Prop :=
  let eb := (F.metric t).orthonormalBasis x
  (Matrix.fromBlocks
    (fun ac bd : (Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) ×
        Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) =>
      (F.connection t).curvatureTensor x (eb ac.1) (eb ac.2)
        (eb bd.1) (eb bd.2))
    (fun (ac : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) ×
        Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) d =>
      hamiltonP (F.connection t) x (eb ac.1) (eb ac.2) (eb d))
    (fun c (bd : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) ×
        Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) =>
      hamiltonP (F.connection t) x (eb bd.1) (eb bd.2) (eb c))
    (fun a b => hamiltonM (F.connection t) τ x (eb a) (eb b))).PosSemidef

theorem finite_differential_of_hamilton_diagonal
    (hC : RicciFlowCurvatureTheory.{u})
    (T₀ T₁ : ℝ) (F : RicciFlow n M (Ioo T₀ T₁))
    (hdiag : ∀ t ∈ Ioo T₀ T₁, ∀ x : M,
      ∀ v : TangentSpace (𝓡 n) x, ∀ i,
      0 ≤ hamiltonM (F.connection t) (t - T₀) x
          ((F.metric t).orthonormalBasis x i)
          ((F.metric t).orthonormalBasis x i) +
        2 * hamiltonP (F.connection t) x v
          ((F.metric t).orthonormalBasis x i)
          ((F.metric t).orthonormalBasis x i) +
        (F.connection t).curvatureTensor x v
          ((F.metric t).orthonormalBasis x i) v
          ((F.metric t).orthonormalBasis x i)) :
    ∀ t ∈ Ioo T₀ T₁, ∀ x : M, ∀ v : TangentSpace (𝓡 n) x,
      ∃ dR : ℝ,
        HasDerivWithinAt (fun s ↦ (F.connection s).scalarCurvature x) dR
          (Ioo T₀ T₁) t ∧
        0 ≤ dR + (F.connection t).scalarCurvature x / (t - T₀) +
          2 * mvfderiv (𝓡 n)
            (fun y ↦ (F.connection t).scalarCurvature y) x v +
          2 * (F.connection t).ricci x v v := by
  intro t ht x v
  apply finite_differential_of_hamilton_diagonal_nonneg hC T₀ T₁ F t ht x v
  exact hdiag t ht x v

theorem finite_differential_of_hamilton_block
    (hC : RicciFlowCurvatureTheory.{u})
    (T₀ T₁ : ℝ) (F : RicciFlow n M (Ioo T₀ T₁))
    (hblock : ∀ t ∈ Ioo T₀ T₁, ∀ x : M,
      HamiltonBlockPos F t x (t - T₀)) :
    ∀ t ∈ Ioo T₀ T₁, ∀ x : M, ∀ v : TangentSpace (𝓡 n) x,
      ∃ dR : ℝ,
        HasDerivWithinAt (fun s ↦ (F.connection s).scalarCurvature x) dR
          (Ioo T₀ T₁) t ∧
        0 ≤ dR + (F.connection t).scalarCurvature x / (t - T₀) +
          2 * mvfderiv (𝓡 n)
            (fun y ↦ (F.connection t).scalarCurvature y) x v +
          2 * (F.connection t).ricci x v v := by
  apply finite_differential_of_hamilton_diagonal hC T₀ T₁ F
  intro t ht x v
  have ht' : t ∈ interior (Ioo T₀ T₁) := by
    simpa only [interior_Ioo] using ht
  let g := F.metric t
  let D := F.connection t
  let b := g.orthonormalBasis x
  have hD := hC.tensor_calculus n M g D
  intro a
  have hP : hamiltonP D x v (b a) (b a) =
      ∑ i, hamiltonP D x (b i) (b a) (b a) * g.inner x v (b i) := by
    simpa [Function.update, b, mul_comm] using
      (hamiltonP_isSmoothCovariantTensor D hD).update_eq_sum g x ![v, b a, b a] 0 v
  have hRfirst : D.curvatureTensor x v (b a) v (b a) =
      ∑ i, g.inner x v (b i) * D.curvatureTensor x (b i) (b a) v (b a) := by
    simpa [LeviCivitaData.riemannEvaluation, Function.update, b] using
      hD.1.update_eq_sum g x ![v, b a, v, b a] 0 v
  have hRthird (i) : D.curvatureTensor x (b i) (b a) v (b a) =
      ∑ k, g.inner x v (b k) * D.curvatureTensor x (b i) (b a) (b k) (b a) := by
    simpa [LeviCivitaData.riemannEvaluation, Function.update, b] using
      hD.1.update_eq_sum g x ![b i, b a, v, b a] 2 v
  have hR : D.curvatureTensor x v (b a) v (b a) =
      ∑ i, ∑ k, D.curvatureTensor x (b i) (b a) (b k) (b a) *
        g.inner x v (b i) * g.inner x v (b k) := by
    rw [hRfirst]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hRthird, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  change 0 ≤ hamiltonM D (t - T₀) x (b a) (b a) +
    2 * hamiltonP D x v (b a) (b a) + D.curvatureTensor x v (b a) v (b a)
  rw [hP, hR]
  exact hamilton_diagonal_nonneg_of_geometric_block hC F
    ht' (t - T₀) x v (hblock t ht x) a

end Poincare.RicciFlow.Harnack
