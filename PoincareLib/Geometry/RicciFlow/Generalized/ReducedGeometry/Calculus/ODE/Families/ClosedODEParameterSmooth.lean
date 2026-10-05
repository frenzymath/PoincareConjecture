import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.SourceNames.LGeometry
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Calculus.ODE.Local.ClosedPicardSmooth
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Calculus.ODE.Local.ClosedPicardEquation

/-!
# Smooth initial-state dependence of an actual closed ODE family

Morgan-Tian Lemma 6.18, pp. 113-114. A supplied continuous path-valued
family satisfies the actual Picard equation. The common implicit-family
uniqueness neighborhood identifies it locally with the smooth family.
Thus the original family is smooth in its initial state, in the sup path
norm, under the explicit short-interval state-derivative bound.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology ContDiff

namespace PoincareMT.M14

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {a b : ℝ}

/-- A continuous family of actual closed-time initial-value solutions
is smooth in the initial state when the reference path satisfies the
explicit smallness bound, the local smooth-dependence assertion of
Lemma 6.18, pp. 113-114. The conclusion is in the sup path norm. -/
theorem closedODEFamily_contDiffAt (hab : a < b) (t₀ : Icc a b)
    (f : ℝ × E → E) (hf : ContDiffOn ℝ ∞ f (Icc a b ×ˢ univ))
    (α : E → C(Icc a b, E)) {x₀ : E} (hα : ContinuousAt α x₀)
    (hi : ∀ᶠ x in 𝓝 x₀, α x t₀ = x)
    (hode : ∀ᶠ x in 𝓝 x₀, ∀ r : Icc a b, HasDerivWithinAt
      (fun s => α x (projIcc a b (t₀.property.1.trans t₀.property.2) s))
      (f (r.val, α x r)) (Icc a b) r.val)
    (hsmall : (b - a) * ‖closedTimePostcomp (M08.spatialWithinFDeriv (Icc a b) univ f)
      (M08.spatialWithinFDeriv_contDiffOn (uniqueDiffOn_Icc hab) isOpen_univ f hf).continuousOn
        (α x₀)‖ < 1) :
    ContDiffAt ℝ ∞ α x₀ := by
  have heq : ∀ᶠ x in 𝓝 x₀, α x = ContinuousMap.const _ x +
      closedPathPrimitive t₀ (closedTimePostcomp f hf.continuousOn (α x)) := by
    filter_upwards [hi, hode] with x hx hd
    have h := closedPath_picard_equation_of_ode t₀ f hf.continuousOn (α x) hd
    rwa [hx] at h
  obtain ⟨σ, U, W, hU, hxU, hW, hxW, _, hσ, _, huniq⟩ :=
    exists_closedPicard_smooth_family hab t₀ f hf x₀ (α x₀) heq.self_of_nhds hsmall
  have hgraph : Tendsto (fun x => (x, α x)) (𝓝 x₀) (𝓝 (x₀, α x₀)) :=
    (continuousAt_id.prodMk hα).tendsto
  have hsame : α =ᶠ[𝓝 x₀] σ := by
    filter_upwards [heq, hgraph.eventually (hW.mem_nhds hxW)] with x hx hxW
    exact ((huniq (x, α x) hxW).mp hx).symm
  exact (hσ.contDiffAt (hU.mem_nhds hxU)).congr_of_eventuallyEq hsame

end PoincareMT.M14
