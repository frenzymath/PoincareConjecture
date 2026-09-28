import PoincareConjecture.Proofs.M07.Geometry.Riemannian.ScalarOperators
import PoincareConjecture.Proofs.M07.Geometry.Manifold.VectorField.Commutator








set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}








lemma hessianOnFields_symm_of_commutator
    (D : LeviCivitaData g) (f : M → ℝ)
    {X Y : (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (htors : D.connection Y x (X x) - D.connection X x (Y x) =
      VectorField.mlieBracket (𝓡 n) X Y x)
    (hcomm :
      mvfderiv (𝓡 n) (fun y ↦ mvfderiv (𝓡 n) f y (Y y)) x (X x) -
          mvfderiv (𝓡 n) (fun y ↦ mvfderiv (𝓡 n) f y (X y)) x (Y x) =
        mvfderiv (𝓡 n) f x (VectorField.mlieBracket (𝓡 n) X Y x)) :
    D.hessianOnFields f X Y x = D.hessianOnFields f Y X x := by
  unfold hessianOnFields
  have hdf := congrArg (fun v ↦ mvfderiv (𝓡 n) f x v) htors
  have hdf' :
      mvfderiv (𝓡 n) f x (D.connection Y x (X x)) -
          mvfderiv (𝓡 n) f x (D.connection X x (Y x)) =
        mvfderiv (𝓡 n) f x (VectorField.mlieBracket (𝓡 n) X Y x) := by
    simpa only [map_sub] using hdf
  linarith

lemma hessian_symm
    (D : LeviCivitaData g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (x : M)
    (u v : TangentSpace (𝓡 n) x) :
    D.hessian f x u v = D.hessian f x v u := by
  let X := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) u
  let Y := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v
  have htors := (CovariantDerivative.torsion_eq_zero_iff D.connection).mp D.torsion_eq_zero
    (FiberBundle.mdifferentiableAt_extend (𝓡 n)
      (EuclideanSpace ℝ (Fin n)) u)
    (FiberBundle.mdifferentiableAt_extend (𝓡 n)
      (EuclideanSpace ℝ (Fin n)) v)
  have hcomm := Poincare.Manifold.VectorField.mfderiv_mlieBracket_eq_commutator
    X Y hf x
      (FiberBundle.mdifferentiableAt_extend (𝓡 n)
        (EuclideanSpace ℝ (Fin n)) u)
      (FiberBundle.mdifferentiableAt_extend (𝓡 n)
        (EuclideanSpace ℝ (Fin n)) v)
  have h := hessianOnFields_symm_of_commutator D f (X := X) (Y := Y) (x := x)
    (by simpa [X, Y] using htors) (by simpa [X, Y] using hcomm.symm)
  simpa [hessian, X, Y] using h

end PoincareConjecture.LeviCivitaData
