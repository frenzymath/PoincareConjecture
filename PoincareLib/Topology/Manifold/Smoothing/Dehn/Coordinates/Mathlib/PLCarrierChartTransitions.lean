import PoincareLib.Topology.Manifold.Smoothing.Dehn.Isotopy.Mathlib.PLCarrierMotionLocal
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Coordinates.Mathlib.SupportedChartInverse
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Coordinates.SupportedChartPLTransition

/-!
# Whole original PL transitions of a transported carrier motion

Each slice and inverse slice use the original atlas and the actual
chart extension. The complete transition sources are retained.
See Hudson1969, Lemma4.6, pp.97--99, and Dehn031, section3.
-/

set_option autoImplicit false

open Set unitInterval

namespace Geometry.PLCarrierMotion

/-- Every original coordinate transition of the extended slice and
its inverse is PL on its whole source. This includes support-boundary
points and uses the actual extension formulas. See Dehn031, section3. -/
theorem chart_transitions {E X ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace X] [T2Space X]
    (J : SimplicialComplex ℝ E) (hJ : J.faces.Finite)
    {P : Set E} {ε : ℝ} (H : PLCarrierMotion J.space P ε)
    (Q : OpenPartialHomeomorph E X) (hJQ : J.space ⊆ Q.source)
    (e : ι → OpenPartialHomeomorph X E)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid E)
    (hQ : ∀ i, (e i).symm.trans Q.symm ∈ piecewiseAffineGroupoid E)
    (t : I) (F : X ≃ₜ X)
    (hFQ : EqOn F (Q.symm.trans ((H.map t).toOpenPartialHomeomorph.trans Q)) Q.target)
    (hFout : EqOn F id (Q '' J.space)ᶜ) :
    (∀ i j, (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈
      piecewiseAffineGroupoid E) ∧
    (∀ i j, (e i).symm.trans (F.symm.toOpenPartialHomeomorph.trans (e j)) ∈
      piecewiseAffineGroupoid E) := by
  have hfix : EqOn (H.map t) id J.spaceᶜ := by
    intro x hx
    exact H.outside t x (fun hi => hx (interior_subset hi))
  have hinvfix : EqOn (H.map t).symm id J.spaceᶜ := by
    intro x hx
    apply (H.map t).injective
    change H.map t ((H.map t).symm x) = H.map t x
    rw [(H.map t).apply_symm_apply, hfix hx]
    rfl
  have hHPL := H.slice_mem_piecewiseAffineGroupoid t
  have hHinvPL : (H.map t).symm.toOpenPartialHomeomorph ∈
      piecewiseAffineGroupoid E := (piecewiseAffineGroupoid E).symm hHPL
  have hinv := Q.supported_chart_symm_eqOn (H.map t) F hJQ hfix hFQ hFout
  constructor
  · intro i j
    exact Q.supported_chart_transition_mem_piecewiseAffineGroupoid
      (e i).symm (e j).symm (H.map t) F (J.isCompact_space_of_finite hJ) hJQ
      hfix hFQ hFout hHPL (hQ i) (hQ j) (he i j)
  · intro i j
    exact Q.supported_chart_transition_mem_piecewiseAffineGroupoid
      (e i).symm (e j).symm (H.map t).symm F.symm
      (J.isCompact_space_of_finite hJ) hJQ hinvfix hinv.1 hinv.2 hHinvPL
      (hQ i) (hQ j) (he i j)

end Geometry.PLCarrierMotion
