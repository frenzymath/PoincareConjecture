import PoincareConjecture.Proofs.M04.SpacetimePairings
import PoincareConjecture.Proofs.M04.TensorDerivativeClosure
import PoincareConjecture.Proofs.M04.ShiCoordinateConnection









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M47

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {U : Set M} {g : RiemannianMetric n M}



theorem contMDiffOn_fixed_covariantTensorDerivative (D : LeviCivitaData g) {k : ℕ}
    {T : ℝ → CovariantTensorEvaluation n M k}
    (hT : ∀ s, IsSmoothCovariantTensor (T s))
    (hTime : ∀ (V : Set M), IsOpen V →
      ∀ (Y : Fin k → (y : M) → TangentSpace (𝓡 n) y),
        (∀ i, ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
          ∞ (T% (Y i)) V) →
        ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × M ↦ T p.1 p.2 (fun i ↦ Y i p.2)) (J ×ˢ V))
    (hU : IsOpen U) {X : Fin (k + 1) → (y : M) → TangentSpace (𝓡 n) y}
    (hX : ∀ i, ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% (X i)) U) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M ↦ D.covariantTensorDerivative (T p.1) p.2
        (fun i ↦ X i p.2)) (J ×ˢ U) := by
  classical
  have hfirst := M04.contMDiffOn_mvfderiv_spatial hU
    (hTime U hU (fun i ↦ X i.succ) (fun i ↦ hX i.succ)) (hX 0)
  have hcorrection (i : Fin k) :
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M ↦ T p.1 p.2 (Function.update (fun j ↦ X j.succ p.2) i
          (D.connection (X i.succ) p.2 (X 0 p.2)))) (J ×ˢ U) := by
    let Z := fun y ↦ D.connection (X i.succ) y (X 0 y)
    have hZ : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        ∞ (T% Z) U := M04.contMDiffOn_shi_connection D hU (hX 0) (hX i.succ)
    have hY (j : Fin k) :
        ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
          ∞ (T% (Function.update (fun l ↦ X l.succ) i Z j)) U := by
      by_cases hj : j = i
      · subst j
        simpa only [Function.update_self] using hZ
      · simpa only [Function.update_of_ne hj] using hX j.succ
    apply (hTime U hU (Function.update (fun j ↦ X j.succ) i Z) hY).congr
    intro p hp
    congr 1
    funext j
    by_cases hj : j = i <;> simp [hj, Z]
  have hsum := contMDiffOn_finsetSum
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin k))) ↦ hcorrection i)
  apply (hfirst.sub hsum).congr
  intro p hp
  exact (M04.covariantTensorDerivativeOnFields_eq D (hT p.1) hU hX hp.2).symm


theorem contMDiffOn_fixed_iteratedCovariantTensorDerivative (D : LeviCivitaData g) {k : ℕ}
    {T : ℝ → CovariantTensorEvaluation n M k}
    (hT : ∀ s, IsSmoothCovariantTensor (T s))
    (hTime : ∀ (V : Set M), IsOpen V →
      ∀ (Y : Fin k → (y : M) → TangentSpace (𝓡 n) y),
        (∀ i, ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
          ∞ (T% (Y i)) V) →
        ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × M ↦ T p.1 p.2 (fun i ↦ Y i p.2)) (J ×ˢ V))
    (m : ℕ) (hU : IsOpen U) {X : Fin (k + m) → (y : M) → TangentSpace (𝓡 n) y}
    (hX : ∀ i, ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% (X i)) U) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M ↦ D.iteratedCovariantTensorDerivative (T p.1) m p.2
        (fun i ↦ X i p.2)) (J ×ˢ U) := by
  have hsmooth (m : ℕ) (s : ℝ) :
      IsSmoothCovariantTensor (D.iteratedCovariantTensorDerivative (T s) m) := by
    induction m with
    | zero => exact hT s
    | succ m ih => exact M04.isSmoothCovariantTensor_covariantTensorDerivative D ih
  induction m generalizing U with
  | zero => exact hTime U hU X hX
  | succ m ih =>
    exact contMDiffOn_fixed_covariantTensorDerivative D (hsmooth m)
      (fun V hV Y hY ↦ ih hV hY) hU hX

end PoincareConjecture.Proofs.M47
