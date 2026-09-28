import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.PlaneFirstVariation
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.ChartHessianConnection











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



noncomputable def m65PlaneHessian {g : RiemannianMetric n M} (D : LeviCivitaData g)
    (f : LoopPlane → M) (x u v : LoopPlane) : TangentSpace (𝓡 n) (f x) :=
  rampHorizontalCovariantDerivative D (fun r => f (x + r • u))
    (fun r => mfderiv (𝓡 2) (𝓡 n) f (x + r • u) v) 0



theorem m65PlaneTension_eq_hessianTrace {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (f : LoopPlane → M) (x : LoopPlane) :
    m65PlaneTension D f x = ∑ i : Fin 2, m65PlaneHessian D f x
      (EuclideanSpace.basisFun (Fin 2) ℝ i) (EuclideanSpace.basisFun (Fin 2) ℝ i) := rfl




theorem m65PlaneDerivative_chart (p : M) {f : LoopPlane → M} {x : LoopPlane}
    (hf : MDifferentiableAt (𝓡 2) (𝓡 n) f x)
    (hx : f x ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source) (v : LoopPlane) :
    Proofs.M09.chartVectorField p
      (fderiv ℝ ((chartAt (EuclideanSpace ℝ (Fin n)) p) ∘ f) x v) (f x) =
        mfderiv (𝓡 2) (𝓡 n) f x v := by
  let c := chartAt (EuclideanSpace ℝ (Fin n)) p
  have hi : (mfderiv (𝓡 n) (𝓡 n) c (f x)).IsInvertible :=
    ⟨(mdifferentiable_chart (I := 𝓡 n) p).mfderiv hx, rfl⟩
  have hc := mfderiv_comp x ((mdifferentiable_chart (I := 𝓡 n) p).mdifferentiableAt hx) hf
  rw [mfderiv_eq_fderiv] at hc
  change (mfderiv (𝓡 n) (𝓡 n) c (f x)).inverse
    (fderiv ℝ (c ∘ f) x v) = mfderiv (𝓡 2) (𝓡 n) f x v
  rw [hc]
  change (mfderiv (𝓡 n) (𝓡 n) c (f x)).inverse
    (mfderiv (𝓡 n) (𝓡 n) c (f x) (mfderiv (𝓡 2) (𝓡 n) f x v)) = _
  exact hi.inverse_apply_self _

end PoincareConjecture
