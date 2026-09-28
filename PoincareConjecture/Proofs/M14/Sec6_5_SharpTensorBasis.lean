import PoincareConjecture.Proofs.M14.Sec6_5_SharpHessianBilinear
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Tensor.Trace
import Mathlib.LinearAlgebra.BilinearForm.Hom

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}

theorem ricci_add_bilinear_eq_of_basis
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) (q : G.Point)
    (B : LinearMap.BilinForm ℝ (G.Horizontal q)) (c : ℝ)
    (b : Module.Basis (Fin n) ℝ (G.Horizontal q))
    (heq : ∀ i j, horizontalRicci G.leafwise q (b i) (b j) + B (b i) (b j) =
      G.spacetime.horizontalMetric.inner q (b i) (b j) / c)
    (v w : G.Horizontal q) :
    horizontalRicci G.leafwise q v w + B v w =
      G.spacetime.horizontalMetric.inner q v w / c := by
  have H := (hM12.leafwise_calculus X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover).2 G.leafwise
  obtain ⟨A, hA⟩ := H.ricci_tensor.1 q
  let C := bilinearOfTensorCons A ![]
  have hC (u z : G.Horizontal q) : C u z = horizontalRicci G.leafwise q u z := by
    change A (Fin.cons u (Fin.cons z ![])) = _
    rw [show Fin.cons u (Fin.cons z ![]) = ![u, z] by
      funext i
      fin_cases i <;> rfl]
    exact (hA ![u, z]).symm
  let M : LinearMap.BilinForm ℝ (G.Horizontal q) :=
    (ContinuousLinearMap.coeLM ℝ).comp (G.spacetime.horizontalMetric.inner q).toLinearMap
  have hM (u z : G.Horizontal q) : M u z = G.spacetime.horizontalMetric.inner q u z := rfl
  have hforms : C + B = c⁻¹ • M := by
    apply LinearMap.BilinForm.ext_basis b
    intro i j
    change C (b i) (b j) + B (b i) (b j) = c⁻¹ * M (b i) (b j)
    rw [hC]
    exact (heq i j).trans (by rw [hM]; ring)
  have hvalue := congrArg (fun F : LinearMap.BilinForm ℝ (G.Horizontal q) => F v w) hforms
  change C v w + B v w = c⁻¹ * M v w at hvalue
  rw [hC] at hvalue
  exact hvalue.trans (by rw [hM]; ring)

end PoincareConjecture.M14
