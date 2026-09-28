import PoincareConjecture.Proofs.M47.BlowupControlsCapGramDerivative

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.M47

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

private theorem coefficient_constant_field_smooth (v : V) :
    ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞
      (fun x : V => Bundle.TotalSpace.mk' V x (E := TangentSpace (𝓡 n)) v) univ := by
  intro x _
  apply ContMDiffAt.contMDiffWithinAt
  rw [Bundle.contMDiffAt_totalSpace]
  exact ⟨contMDiffAt_id, by simpa using contMDiffAt_const (c := v)⟩

theorem cap_connectionDifference_coefficients
    {g0 g1 : RiemannianMetric n V} (D0 : LeviCivitaData g0) (D1 : LeviCivitaData g1)
    (e : V ≃L[ℝ] V) (x u v : V) (i : Fin n) :
    let b := EuclideanSpace.basisFun (Fin n) ℝ
    let H : CovariantTensorEvaluation n V 2 :=
      fun y z => g1.inner y (z 0) (z 1) - g0.inner y (z 0) (z 1)
    inner ℝ (b i) (e.symm (D1.euclideanConnection u v x - D0.euclideanConnection u v x)) =
      (1 / 2 : ℝ) * ∑ j, M04.frameInverseGram g1 x e.toContinuousLinearMap i j *
        (D0.covariantTensorDerivative H x ![u, v, e (b j)] +
          D0.covariantTensorDerivative H x ![v, u, e (b j)] -
          D0.covariantTensorDerivative H x ![e (b j), u, v]) := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let H : CovariantTensorEvaluation n V 2 :=
    fun y z => g1.inner y (z 0) (z 1) - g0.inner y (z 0) (z 1)
  have hconst (w : V) : MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n))
      (fun y : V => Bundle.TotalSpace.mk' V y (E := TangentSpace (𝓡 n)) w) x :=
    ((coefficient_constant_field_smooth w).contMDiffAt (by simp)).mdifferentiableAt (by simp)
  have hd (a c d : V) :
      M04.covariantTensorDerivativeOnFields D0 H
        ![fun _ => a, fun _ => c, fun _ => d] x =
      D0.covariantTensorDerivative H x ![a, c, d] := by
    apply M04.covariantTensorDerivativeOnFields_eq D0 (cap_metricDifference_smooth g0 g1)
      isOpen_univ _ (mem_univ x)
    intro k
    fin_cases k <;> exact coefficient_constant_field_smooth _
  have h := cap_connection_difference_components D0 D1 e
    (fun j _ => e (b j)) (hconst u) (hconst v) (fun j => hconst (e (b j)))
    (fun _ => rfl) i
  dsimp only at h ⊢
  dsimp only [H, b] at hd
  simp only [hd] at h
  convert! h using 1

end PoincareConjecture.M47
