import PoincareLib.Geometry.CurveShortening.Deformation.Compatibility.SourceNames
import PoincareLib.Geometry.CurveShortening.Deformation.MinimalDisk.PlaneFirstVariation
import PoincareLib.Geometry.CurveShortening.Deformation.MinimalDisk.ChartHessianConnection

/-!
# The genuine covariant Hessian of the supplied disk

The definition uses the frozen pullback connection on actual differential
columns along parameter lines. Its Euclidean trace is exactly the actual
harmonic tension already used in first variation.
Source: Morgan--Tian Lemma 19.2, printed p. 438;
M65 derivation 24, twelfth stage.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareMT

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- Covariant differentiation of the actual differential column along a
parameter line. Source: MT Lemma 19.2, p. 438; derivation 24, twelfth stage. -/
noncomputable def m65PlaneHessian {g : RiemannianMetric n M} (D : LeviCivitaData g)
    (f : LoopPlane → M) (x u v : LoopPlane) : TangentSpace (𝓡 n) (f x) :=
  rampHorizontalCovariantDerivative D (fun r => f (x + r • u))
    (fun r => mfderiv (𝓡 2) (𝓡 n) f (x + r • u) v) 0

/-- The actual tension is the Euclidean trace of the genuine Hessian.
Source: MT Lemma 19.2, p. 438; derivation 24, twelfth stage. -/
theorem m65PlaneTension_eq_hessianTrace {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (f : LoopPlane → M) (x : LoopPlane) :
    m65PlaneTension D f x = ∑ i : Fin 2, m65PlaneHessian D f x
      (EuclideanSpace.basisFun (Fin 2) ℝ i) (EuclideanSpace.basisFun (Fin 2) ℝ i) := rfl

/-- The genuine coordinate derivative reconstructs the actual disk
differential through the actual chart vector field. Source: MT Lemma 19.2,
p. 438; derivation 24, twelfth stage. -/
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

end PoincareMT
