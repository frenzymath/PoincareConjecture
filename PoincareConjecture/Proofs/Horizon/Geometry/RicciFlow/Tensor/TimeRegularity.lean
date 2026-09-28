import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.ContDiff.TimeDerivative
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Regularity
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology BigOperators
open Filter Set

universe u

namespace PoincareConjecture.RicciFlow

open PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

lemma isSmoothCovariantTensor_timeDerivative_all
    {k : ℕ} {T W : ℝ → CovariantTensorEvaluation n M k} {t : ℝ}
    (hT : ∀ s, IsSmoothCovariantTensor (T s))
    (hreg : ∀ (y : M) (X : Fin k → (z : M) → TangentSpace (𝓡 n) z),
      (∀ i, ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
        (T% (X i)) y) →
      ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => T p.1 p.2 (fun i => X i p.2)) (t, y))
    (hW : ∀ (y : M) (z : Fin k → TangentSpace (𝓡 n) y),
      HasDerivAt (fun s => T s y z) (W t y z) t) :
    IsSmoothCovariantTensor (W t) := by
  constructor
  · intro x
    let A : MultilinearMap ℝ (fun _ : Fin k ↦ TangentSpace (𝓡 n) x) ℝ :=
      { toFun := W t x
        map_update_add' {hDecEq} := by
          intro v i p q
          have hEq : (fun s : ℝ => T s x (Function.update v i (p + q))) =
              (fun s : ℝ => T s x (Function.update v i p)) +
                (fun s : ℝ => T s x (Function.update v i q)) := by
            funext s
            obtain ⟨B, hB⟩ := (hT s).1 x
            change T s x (Function.update v i (p + q)) =
              T s x (Function.update v i p) + T s x (Function.update v i q)
            rw [hB, hB, hB, B.map_update_add]
          have hl := hW x (Function.update v i (p + q))
          have hr := (hW x (Function.update v i p)).add
            (hW x (Function.update v i q))
          have hr' := hr.congr_of_eventuallyEq
            (Eventually.of_forall (fun s => congrFun hEq s))
          exact hl.unique hr'
        map_update_smul' {hDecEq} := by
          intro v i c p
          have hEq : (fun s : ℝ => T s x (Function.update v i (c • p))) =
              c • (fun s : ℝ => T s x (Function.update v i p)) := by
            funext s
            obtain ⟨B, hB⟩ := (hT s).1 x
            change T s x (Function.update v i (c • p)) =
              c * T s x (Function.update v i p)
            rw [hB, hB, B.map_update_smul]
            simp [smul_eq_mul]
          have hl := hW x (Function.update v i (c • p))
          have hr := (hW x (Function.update v i p)).const_smul c
          have hr' := hr.congr_of_eventuallyEq
            (Eventually.of_forall (fun s => congrFun hEq s))
          exact hl.unique hr' }
    exact ⟨A, fun v => rfl⟩
  · intro U hU X hX x hx
    have hXx (i : Fin k) :
        ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
          (T% (X i)) x :=
      (hX i).contMDiffAt (hU.mem_nhds hx)
    have hsp := hreg x X hXx
    have hdfun : (fun y : M => deriv (fun s => T s y (fun i => X i y)) t) =
        (fun y => W t y (fun i => X i y)) := by
      funext y
      exact (hW y (fun i => X i y)).deriv
    have hcont := Poincare.Manifold.contMDiffAt_deriv_time hsp
    change ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => deriv (fun s => T s p.2 (fun i => X i p.2)) p.1) (t, x) at hcont
    have hcontx := hcont.comp x (contMDiffAt_const.prodMk contMDiffAt_id)
    change ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y => deriv (fun s => T s y (fun i => X i y)) t) x at hcontx
    rw [hdfun] at hcontx
    exact hcontx.contMDiffWithinAt

lemma isSmoothCovariantTensor_timeDerivative
    {T W : ℝ → CovariantTensorEvaluation n M 2} {t : ℝ}
    (hT : ∀ s, IsSmoothCovariantTensor (T s))
    (hreg : ∀ (y : M) (X Y : (z : M) → TangentSpace (𝓡 n) z),
      ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) y →
      ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) y →
      ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => T p.1 p.2 ![X p.2, Y p.2]) (t, y))
    (hW : ∀ (y : M) (z : Fin 2 → TangentSpace (𝓡 n) y),
      HasDerivAt (fun s => T s y z) (W t y z) t) :
    IsSmoothCovariantTensor (W t) := by
  apply isSmoothCovariantTensor_timeDerivative_all hT _ hW
  intro y X hX
  have h := hreg y (X 0) (X 1) (hX 0) (hX 1)
  convert h using 1
  ext p
  congr 1
  ext i; fin_cases i <;> rfl

end PoincareConjecture.RicciFlow
