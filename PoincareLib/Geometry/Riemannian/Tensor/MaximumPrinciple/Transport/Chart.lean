import PoincareLib.Geometry.Riemannian.Tensor.MaximumPrinciple.Transport.Coordinates
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-! # Differentiation in the tangent trivialization

The tangent trivialization is the derivative of the corresponding chart.
Thus differentiating a vector-valued function on the manifold agrees with
ordinary differentiation of its chart representative, applied to the
trivialized tangent direction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Topology

namespace PoincareMT.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- The tangent trivialization converts the manifold differential to the
ordinary derivative of a chart representative. -/
lemma mvfderiv_eq_chart_fderiv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (p : M) {f : M → F} {x : M} (hx : x ∈ (extChartAt (𝓡 n) p).source)
    (hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, F) f x) (u : TangentSpace (𝓡 n) x) :
    mvfderiv (𝓡 n) f x u =
      fderiv ℝ (f ∘ (extChartAt (𝓡 n) p).symm) (extChartAt (𝓡 n) p x)
        ((trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p).continuousLinearMapAt
          ℝ x u) := by
  let e := extChartAt (𝓡 n) p
  have hxc : x ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source := by simpa using hx
  have hs : MDifferentiableAt (𝓡 n) (𝓡 n) e.symm (e x) := by
    have h := mdifferentiableWithinAt_extChartAt_symm (I := 𝓡 n) (e.map_source hx)
    exact h.mdifferentiableAt (by simp)
  have hfc : MDifferentiableAt (𝓡 n) 𝓘(ℝ, F) (f ∘ e.symm) (e x) := by
    apply MDifferentiableAt.comp (I' := 𝓡 n) (e x) _ hs
    simpa only [e.left_inv hx] using hf
  have heq : ((f ∘ e.symm) ∘ e) =ᶠ[𝓝 x] f := by
    filter_upwards [(extChartAt_source_mem_nhds' hx)] with y hy
    simp only [Function.comp_apply, e.left_inv hy]
  have hd := heq.mfderiv_eq (I := 𝓡 n) (I' := 𝓘(ℝ, F))
  have hc := mfderiv_comp_apply x hfc (mdifferentiableAt_extChartAt hxc) u
  change mvfderiv (𝓡 n) ((f ∘ e.symm) ∘ e) x u = _ at hc
  have hm : mvfderiv (𝓡 n) ((f ∘ e.symm) ∘ e) x = mvfderiv (𝓡 n) f x := by
    unfold mvfderiv
    rw [hd]
    congr 2
  rw [hm] at hc
  rw [TangentBundle.continuousLinearMapAt_trivializationAt hxc]
  simp only [mvfderiv, mfderiv_eq_fderiv, e] at hc
  convert hc using 1 <;> rfl

/-- Coordinate differentiation of a local section uses the same chart as the
coefficient formula for the retained connection. -/
lemma coordinateRepresentative_mvfderiv_eq_fderiv
    (p : M) {Y : (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (hx : x ∈ (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p).baseSet)
    (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) (T% Y) x)
    (u : TangentSpace (𝓡 n) x) :
    mvfderiv (𝓡 n) (coordinateRepresentative p Y) x u =
      fderiv ℝ (coordinateRepresentative p Y ∘ (extChartAt (𝓡 n) p).symm)
        (extChartAt (𝓡 n) p x)
        ((trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p).continuousLinearMapAt
          ℝ x u) := by
  apply mvfderiv_eq_chart_fderiv p _ (mdifferentiableAt_coordinateRepresentative p hx hY) u
  simpa using hx

end PoincareMT.LeviCivitaData
