import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_ConnectionDifference
import PoincareConjecture.Proofs.M44.Mathlib.ConnectionCurvatureDifference

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.M44

open CoordinateExponential

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace

local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem contDiff_connectionDifference (g h : RiemannianMetric 3 E) :
    ContDiff ℝ ∞ (connectionDifference g h) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  exact (contDiffAt_christoffelBilinear (h.contDiffAt_euclideanCoefficients x)
    (h.inner_isInvertible x)).sub
    (contDiffAt_christoffelBilinear (g.contDiffAt_euclideanCoefficients x)
      (g.inner_isInvertible x))

noncomputable def covariantConnectionDifference (g h : RiemannianMetric 3 E)
    (x d u v : E) : E :=
  fderiv ℝ (connectionDifference g h) x d u v +
    christoffelBilinear g.euclideanCoefficients x d (connectionDifference g h x u v) -
    connectionDifference g h x (christoffelBilinear g.euclideanCoefficients x d u) v -
    connectionDifference g h x u (christoffelBilinear g.euclideanCoefficients x d v)

theorem curvature_eq_add_connectionDifference {g h : RiemannianMetric 3 E}
    (D : LeviCivitaData g) (D' : LeviCivitaData h) (x u v w : E) :
    (D'.curvature x u v w : E) = HAdd.hAdd (α := E) (β := E) (γ := E) (D.curvature x u v w)
      (covariantConnectionDifference g h x u v w -
        covariantConnectionDifference g h x v u w) +
      (connectionDifference g h x u (connectionDifference g h x v w) -
        connectionDifference g h x v (connectionDifference g h x u w)) := by
  have hg := (contDiffAt_christoffelBilinear (g.contDiffAt_euclideanCoefficients x)
    (g.inner_isInvertible x)).differentiableAt (by simp)
  have hh := (contDiffAt_christoffelBilinear (h.contDiffAt_euclideanCoefficients x)
    (h.inner_isInvertible x)).differentiableAt (by simp)
  rw [← coordinateCurvature_eq_retained D', ← coordinateCurvature_eq_retained D,
    coordinateCurvature_eq_christoffelCurvature hh,
    coordinateCurvature_eq_christoffelCurvature hg]
  have hs := christoffelBilinear_symm
    ((g.contDiffAt_euclideanCoefficients x).differentiableAt (by simp))
    (Filter.Eventually.of_forall fun y a b => g.symm y a b) u v
  have hdiff : fderiv ℝ (connectionDifference g h) x =
      fderiv ℝ (christoffelBilinear h.euclideanCoefficients) x -
      fderiv ℝ (christoffelBilinear g.euclideanCoefficients) x := fderiv_fun_sub hh hg
  simp only [covariantConnectionDifference, hdiff, connectionDifference,
    ConnectionVariation.christoffelCurvature]
  convert connection_curvature_difference_algebra
      (christoffelBilinear g.euclideanCoefficients x)
      (christoffelBilinear h.euclideanCoefficients x)
      (fderiv ℝ (christoffelBilinear g.euclideanCoefficients) x)
      (fderiv ℝ (christoffelBilinear h.euclideanCoefficients) x) u v w hs using 1

noncomputable def koszulPermutation (T : CovariantTensorEvaluation 3 E 3) :
    CovariantTensorEvaluation 3 E 3 := fun x v =>
  T x v + T x (v ∘ (Equiv.swap 0 1).trans (Equiv.swap 0 2)) -
    T x (v ∘ (Equiv.swap 0 2).trans (Equiv.swap 0 1))

theorem koszulPermutation_apply (T : CovariantTensorEvaluation 3 E 3) (x u v w : E) :
    koszulPermutation T x ![u, v, w] =
      T x ![u, v, w] + T x ![v, w, u] - T x ![w, u, v] := by
  have h1 : (![u, v, w] ∘ (Equiv.swap 0 1).trans (Equiv.swap 0 2)) = ![v, w, u] := by
    funext i
    fin_cases i <;> simp! [Equiv.swap_apply_def, Fin.ext_iff]
  have h2 : (![u, v, w] ∘ (Equiv.swap 0 2).trans (Equiv.swap 0 1)) = ![w, u, v] := by
    funext i
    fin_cases i <;> simp! [Equiv.swap_apply_def, Fin.ext_iff]
  simp only [koszulPermutation, h1, h2]

theorem koszulPermutation_isSmooth {T : CovariantTensorEvaluation 3 E 3}
    (hT : IsSmoothCovariantTensor T) : IsSmoothCovariantTensor (koszulPermutation T) :=
  (hT.add (hT.perm ((Equiv.swap 0 1).trans (Equiv.swap 0 2)))).sub
    (hT.perm ((Equiv.swap 0 2).trans (Equiv.swap 0 1)))

theorem covariant_koszulPermutation {g : RiemannianMetric 3 E} (D : LeviCivitaData g)
    {T : CovariantTensorEvaluation 3 E 3} (hT : IsSmoothCovariantTensor T)
    (x d u v w : E) :
    D.covariantTensorDerivative (koszulPermutation T) x ![d, u, v, w] =
      D.covariantTensorDerivative T x ![d, u, v, w] +
      D.covariantTensorDerivative T x ![d, v, w, u] -
      D.covariantTensorDerivative T x ![d, w, u, v] := by
  unfold koszulPermutation
  rw [D.covariantTensorDerivative_sub
    (hT.add (hT.perm ((Equiv.swap 0 1).trans (Equiv.swap 0 2))))
    (hT.perm ((Equiv.swap 0 2).trans (Equiv.swap 0 1))),
    D.covariantTensorDerivative_add hT
      (hT.perm ((Equiv.swap 0 1).trans (Equiv.swap 0 2)))]
  simp only [D.covariantTensorDerivative_reindex, Matrix.cons_val_zero]
  have hp1 : Fin.cons d (fun i : Fin 3 =>
      (![d, u, v, w] : Fin 4 → E)
        (((Equiv.swap 0 1).trans (Equiv.swap 0 2)) i).succ) = ![d, v, w, u] := by
    funext i
    fin_cases i <;> rfl
  have hp2 : Fin.cons d (fun i : Fin 3 =>
      (![d, u, v, w] : Fin 4 → E)
        (((Equiv.swap 0 2).trans (Equiv.swap 0 1)) i).succ) = ![d, w, u, v] := by
    funext i
    fin_cases i <;> rfl
  erw [hp1, hp2]

end PoincareConjecture.M44
