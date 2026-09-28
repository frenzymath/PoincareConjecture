import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Evolution.Connection.CurvatureFirstVariation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Evolution.Tensor.RicciTraceVariation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Calculus.Identities.ScalarContractions
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Positivity.RicciReactionSymmetry

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators
open Set Topology Filter

universe u

namespace PoincareConjecture.RicciFlowAnalysis

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

set_option maxHeartbeats 2000000 in

set_option backward.isDefEq.respectTransparency false in
theorem hasDerivAt_ricci_evolution (F : RicciFlow n M J)
    {t : ℝ} (ht : t ∈ interior J) (x : M)
    (u v : TangentSpace (𝓡 n) x) :
    HasDerivAt (fun s ↦ (F.connection s).ricci x u v)
      ((F.connection t).tensorLaplacian (F.connection t).ricciEvaluation x ![u, v] +
        (F.connection t).ricciReaction x u v) t := by
  classical
  let g := F.metric t
  let D := F.connection t
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let E := TangentSpace (𝓡 n) x
  let e := g.orthonormalBasis x
  let H := D.iteratedCovariantTensorDerivative D.ricciEvaluation 2 x
  let V (a b c d : E) :=
    -2 * D.ricci x (D.curvature x a b d) c - H ![a, b, d, c] - H ![a, d, b, c] +
      H ![a, c, b, d] + H ![b, a, d, c] + H ![b, d, a, c] - H ![b, c, a, d]
  let S (a c : E) := ∑ i, ∑ j, D.curvatureTensor x a (e i) c (e j) * D.ricci x (e i) (e j)
  let Q (a c : E) := ∑ i, D.ricci x a (e i) * D.ricci x (e i) c
  let C (a c : E) := ∑ i, H ![e i, a, e i, c]
  let L (a c : E) := ∑ i, H ![e i, e i, a, c]
  let r (a c : E) := (∑ i, V a (e i) c (e i)) + 2 * S a c
  have hr (a c : E) : HasDerivAt (fun s ↦ (F.connection s).ricci x a c) (r a c) t := by
    have hd := hasDerivAt_ricci_of_curvature_derivative F x a c
      (fun b d ↦ V a b c d) ht
      (fun b d ↦ hasDerivAt_curvatureTensor_first_variation F ht x a b c d)
    apply hd.congr_deriv
    change (∑ i, V a (e i) c (e i)) +
      2 * (∑ i, ∑ j, D.ricci x (e i) (e j) * D.curvatureTensor x a (e i) c (e j)) = r a c
    dsimp only [r, S]
    congr 1
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    exact mul_comm _ _
  have hRicExpand (a c : E) :
      D.ricci x a c = ∑ j, g.inner x (e j) a * D.ricci x (e j) c := by
    obtain ⟨P, hP⟩ := (isSmoothCovariantTensor_ricciEvaluation D).1 x
    let R := P.toLinearMap ![0, c] 0
    have hR (a : E) : R a = D.ricci x a c := by
      have hu : Function.update ![0, c] 0 a = ![a, c] := by
        funext i
        fin_cases i <;> simp [Function.update]
      change P (Function.update ![0, c] 0 a) = D.ricci x a c
      rw [hu]
      exact (hP ![a, c]).symm
    calc
      D.ricci x a c = R a := (hR a).symm
      _ = R (∑ j, inner ℝ (e j) a • e j) := congrArg R (e.sum_repr' a).symm
      _ = ∑ j, inner ℝ (e j) a * D.ricci x (e j) c := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [map_smul, hR]
        rfl
      _ = _ := rfl
  have hmetric (a c : E) :
      (∑ i, D.ricci x (D.curvature x a (e i) (e i)) c) = Q a c := by
    calc
      _ = ∑ i, ∑ j, D.curvatureTensor x a (e i) (e j) (e i) * D.ricci x (e j) c := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hRicExpand]
        apply Finset.sum_congr rfl
        intro j hj
        rw [g.symm]
        rfl
      _ = Q a c := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j hj
        rw [← Finset.sum_mul]
        rfl
  have hdiv (a c : E) :
      (∑ i, H ![a, e i, e i, c]) = (1 / 2 : ℝ) * D.hessian D.scalarCurvature x a c :=
    ricci_secondCovariantDerivative_contracted D x a c
  have htrace (a c : E) :
      (∑ i, H ![a, c, e i, e i]) = D.hessian D.scalarCurvature x a c :=
    ricci_secondCovariantDerivative_metric_trace D x a c
  have hV (a c : E) (i) :
      V a (e i) c (e i) = -2 * D.ricci x (D.curvature x a (e i) (e i)) c -
        2 * H ![a, e i, e i, c] + H ![a, c, e i, e i] +
          H ![e i, a, e i, c] + H ![e i, e i, a, c] - H ![e i, c, e i, a] := by
    have hs : H ![e i, c, a, e i] = H ![e i, c, e i, a] :=
      ricci_secondCovariantDerivative_symm D x (e i) c a (e i)
    dsimp only [V]
    rw [hs]
    ring
  have hform (a c : E) : r a c = D.ricciReaction x a c + L a c + C a c - C c a := by
    have hsum : (∑ i, V a (e i) c (e i)) = -2 * Q a c + C a c + L a c - C c a := by
      simp only [hV, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      rw [hmetric, hdiv, htrace]
      dsimp only [C, L]
      ring
    have hreaction : D.ricciReaction x a c = 2 * S a c - 2 * Q a c := rfl
    dsimp only [r]
    rw [hsum, hreaction]
    ring
  have hLsym (a c : E) : L a c = L c a := by
    apply Finset.sum_congr rfl
    intro i hi
    exact ricci_secondCovariantDerivative_symm D x (e i) (e i) a c
  have hrsym (a c : E) : r a c = r c a := by
    have heq : (fun s ↦ (F.connection s).ricci x c a) =
        (fun s ↦ (F.connection s).ricci x a c) := by
      funext s
      exact ricci_symm (F.connection s) x c a
    have hd := hr c a
    rw [heq] at hd
    exact (hr a c).unique hd
  have hevol : r u v = D.ricciReaction x u v + L u v := by
    have h1 := hform u v
    have h2 := hform v u
    rw [hrsym v u, ricciReaction_symm D x v u, hLsym v u] at h2
    linarith only [h1, h2]
  have hL : L u v = D.tensorLaplacian D.ricciEvaluation x ![u, v] := by
    rfl
  apply (hr u v).congr_deriv
  rw [hevol, hL, add_comm]

end PoincareConjecture.RicciFlowAnalysis
