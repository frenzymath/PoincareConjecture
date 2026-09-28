import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.IntrinsicCalculus
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.ContractedBianchi
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.TraceRegularity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Linearity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Hessian.Tensor

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

noncomputable def ricciConnectionVariation (D : LeviCivitaData g) :
    CovariantTensorEvaluation n M 3 := fun x v =>
  -D.covariantTensorDerivative D.ricciEvaluation x ![v 0, v 1, v 2] -
    D.covariantTensorDerivative D.ricciEvaluation x ![v 1, v 0, v 2] +
    D.covariantTensorDerivative D.ricciEvaluation x ![v 2, v 0, v 1]

theorem ricciConnectionVariation_apply (D : LeviCivitaData g) (x : M)
    (a b c : TangentSpace (𝓡 n) x) :
    D.ricciConnectionVariation x ![a, b, c] =
      -D.covariantTensorDerivative D.ricciEvaluation x ![a, b, c] -
        D.covariantTensorDerivative D.ricciEvaluation x ![b, a, c] +
        D.covariantTensorDerivative D.ricciEvaluation x ![c, a, b] := rfl

theorem ricciConnectionVariation_isSmooth (D : LeviCivitaData g) :
    IsSmoothCovariantTensor D.ricciConnectionVariation := by
  let σ : Equiv.Perm (Fin 3) := (Equiv.swap 0 2).trans (Equiv.swap 0 1)
  have h := D.covariantTensorDerivative_isSmooth D.ricciEvaluation_isSmooth_manifold
  convert ((h.const_mul (-1)).sub (h.perm (Equiv.swap 0 1))).add (h.perm σ) using 1
  funext x v
  have h0 : ![v 0, v 1, v 2] = v := by ext i; fin_cases i <;> rfl
  have h1 : ![v 1, v 0, v 2] = v ∘ Equiv.swap 0 1 := by
    ext i; fin_cases i <;> simp [Equiv.swap_apply_def]
  have h2 : ![v 2, v 0, v 1] = v ∘ σ := by
    ext i; fin_cases i <;> simp [σ, Equiv.swap_apply_def]
  simp only [ricciConnectionVariation, h0, h1, h2, neg_one_mul]

private theorem covector_eq_of_basis {S T : CovariantTensorEvaluation n M 1}
    (hS : IsSmoothCovariantTensor S) (hT : IsSmoothCovariantTensor T)
    (x : M) (heq : ∀ i, S x ![g.orthonormalBasis x i] =
      T x ![g.orthonormalBasis x i]) (v : Fin 1 → TangentSpace (𝓡 n) x) :
    S x v = T x v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨A, hA⟩ := hS.1 x
  obtain ⟨B, hB⟩ := hT.1 x
  let a := A.toLinearMap v 0
  let b := B.toLinearMap v 0
  have ha (w : TangentSpace (𝓡 n) x) : a w = S x ![w] := by
    change A (Function.update v 0 w) = _
    rw [hA]
    congr 1
    ext i; fin_cases i; simp
  have hb (w : TangentSpace (𝓡 n) x) : b w = T x ![w] := by
    change B (Function.update v 0 w) = _
    rw [hB]
    congr 1
    ext i; fin_cases i; simp
  have he : a = b := (g.orthonormalBasis x).toBasis.ext (fun i => by
    simpa only [ha, hb, OrthonormalBasis.coe_toBasis] using heq i)
  have hv : v = ![v 0] := by ext i; fin_cases i; rfl
  rw [hv, ← ha, ← hb, he]

theorem tensorTrace_ricciConnectionVariation (D : LeviCivitaData g) :
    g.tensorTrace D.ricciConnectionVariation = fun _ _ => 0 := by
  funext x v
  have hz : IsSmoothCovariantTensor (n := n) (k := 1) (fun (_ : M) _ => (0 : ℝ)) := by
    simpa only [zero_mul] using
      ((differentialEvaluation_isSmooth D.contMDiff_scalarCurvature).const_mul 0)
  apply covector_eq_of_basis (g := g)
    (D.ricciConnectionVariation_isSmooth.tensorTrace (g := g)) hz x ?_ v
  intro j
  change (∑ i, D.ricciConnectionVariation x
    ![g.orthonormalBasis x i, g.orthonormalBasis x i, g.orthonormalBasis x j]) = 0
  simp only [D.ricciConnectionVariation_apply, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  simp_rw [D.covariantTensorDerivative_ricciEvaluation_symm
    D.intrinsicCurvatureTensorCalculus x (g.orthonormalBasis x _) (g.orthonormalBasis x _)
      (g.orthonormalBasis x j)]
  change -(∑ i, D.frameRicciDerivative x i j i) -
    (∑ i, D.frameRicciDerivative x i j i) + (∑ i, D.frameRicciDerivative x j i i) = 0
  rw [D.frameRicciDerivative_trace D.intrinsicCurvatureTensorCalculus,
    D.frameRicciDerivative_scalar_trace D.intrinsicCurvatureTensorCalculus]
  ring

theorem sum_ricciConnectionVariation_first_last (D : LeviCivitaData g)
    (x : M) (u : TangentSpace (𝓡 n) x) :
    (∑ i, D.ricciConnectionVariation x
      ![g.orthonormalBasis x i, u, g.orthonormalBasis x i]) =
      -mvfderiv (𝓡 n) D.scalarCurvature x u := by
  simp only [D.ricciConnectionVariation_apply, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  rw [D.sum_covariantTensorDerivative_ricci_eq_scalar_derivative
    D.intrinsicCurvatureTensorCalculus]
  simp_rw [D.covariantTensorDerivative_ricciEvaluation_symm
    D.intrinsicCurvatureTensorCalculus x (g.orthonormalBasis x _) (g.orthonormalBasis x _) u]
  ring

theorem sum_covariantDerivative_ricciConnectionVariation_first_two
    (D : LeviCivitaData g) (x : M) (u v : TangentSpace (𝓡 n) x) :
    (∑ i, D.covariantTensorDerivative D.ricciConnectionVariation x
      ![u, g.orthonormalBasis x i, g.orthonormalBasis x i, v]) = 0 := by
  have h := D.covariantTensorDerivative_tensorTrace D.ricciConnectionVariation_isSmooth x u ![v]
  rw [D.tensorTrace_ricciConnectionVariation] at h
  change D.covariantTensorDerivative (fun _ _ => 0) x ![u, v] =
    (∑ i, D.covariantTensorDerivative D.ricciConnectionVariation x
      ![u, g.orthonormalBasis x i, g.orthonormalBasis x i, v]) at h
  rw [← h]
  simp [covariantTensorDerivative, mvfderiv_const]

theorem sum_covariantDerivative_ricciConnectionVariation_first_last
    (D : LeviCivitaData g) (x : M) (u v : TangentSpace (𝓡 n) x) :
    (∑ i, D.covariantTensorDerivative D.ricciConnectionVariation x
      ![u, g.orthonormalBasis x i, v, g.orthonormalBasis x i]) =
      -D.hessian D.scalarCurvature x u v := by
  let σ : Equiv.Perm (Fin 3) := Equiv.swap 1 2
  let T : CovariantTensorEvaluation n M 3 := fun y w => D.ricciConnectionVariation y (w ∘ σ)
  have hp (y : M) (a b c : TangentSpace (𝓡 n) y) :
      ![a, b, c] ∘ σ = ![a, c, b] := by
    ext i; fin_cases i <;> simp [σ, Equiv.swap_apply_def]
  have htrace : g.tensorTrace T = fun y w => -mvfderiv (𝓡 n) D.scalarCurvature y (w 0) := by
    funext y w
    change (∑ i, T y ![g.orthonormalBasis y i, g.orthonormalBasis y i, w 0]) = _
    simp only [T, hp]
    exact D.sum_ricciConnectionVariation_first_last y (w 0)
  have h := D.covariantTensorDerivative_tensorTrace
    (D.ricciConnectionVariation_isSmooth.perm σ) x u ![v]
  change D.covariantTensorDerivative (g.tensorTrace T) x ![u, v] = _ at h
  rw [htrace] at h
  have hd (a b c : TangentSpace (𝓡 n) x) :
      D.covariantTensorDerivative T x ![u, a, b, c] =
        D.covariantTensorDerivative D.ricciConnectionVariation x ![u, a, c, b] := by
    rw [show T = (fun y w => D.ricciConnectionVariation y (w ∘ σ)) from rfl,
      D.covariantTensorDerivative_reindex]
    change D.covariantTensorDerivative D.ricciConnectionVariation x
      (Fin.cons u (![a, b, c] ∘ σ)) = _
    rw [hp]
    rfl
  change _ = ∑ i, D.covariantTensorDerivative T x
    ![u, g.orthonormalBasis x i, g.orthonormalBasis x i, v] at h
  simp only [hd] at h
  rw [← h]
  have hn := congrArg (fun S => S x ![u, v])
    (D.covariantTensorDerivative_const_mul
      (differentialEvaluation_isSmooth D.contMDiff_scalarCurvature) (-1))
  simpa only [neg_one_mul, ← D.hessian_eq_covariantTensorDerivative,
    differentialEvaluation] using hn

end PoincareConjecture.LeviCivitaData
