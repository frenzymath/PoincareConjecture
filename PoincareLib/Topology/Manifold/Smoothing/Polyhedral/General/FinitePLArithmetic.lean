import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.FinitePLPositivePart
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Coordinates.FinitePLCoordinates
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Simplicial.CommonSimplicialRefinement

/-!
# Arithmetic on actual finite PL carriers

One common subdivision supports products and affine combinations
of two finite PL maps. These formulas are used for the annular
strip in Hatcher's punctured-torus immersion, p. 7, as required
by Hamilton 1976, p. 66. See Hudson 1969, pp. 12--19 and
M76 derivation 270.
-/

set_option autoImplicit false

open Set

namespace Geometry

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

variable [FiniteDimensional ℝ E]

/-- Two finite PL maps on the same actual carrier have a
finite PL product. No target injectivity is required.
See Hudson pp. 12--19 and M76 derivation 270. -/
theorem FinitePiecewiseAffineOn.prod_mk {f : E → F} {g : E → G} {S : Set E}
    (hf : FinitePiecewiseAffineOn f S) (hg : FinitePiecewiseAffineOn g S) :
    FinitePiecewiseAffineOn (fun x => (f x, g x)) S := by
  obtain ⟨K, hK, hKS, hfK⟩ := hf
  obtain ⟨L, hL, hLS, hgL⟩ := hg
  obtain ⟨R, hR, hRK, hRL⟩ :=
    SimplicialComplex.exists_common_finite_subdivision K L hK hL (hKS.trans hLS.symm)
  refine ⟨R, hR, hRK.space_eq.trans hKS, fun s hs => ?_⟩
  obtain ⟨a, ha⟩ := hRK.affineOnFaces hfK s hs
  obtain ⟨b, hb⟩ := hRL.affineOnFaces hgL s hs
  exact ⟨a.prod b, fun x hx => Prod.ext (ha hx) (hb hx)⟩

/-- Sums use a common finite source subdivision, so the
original carrier is unchanged. See Hudson pp. 12--19 and
M76 derivation 270. -/
theorem FinitePiecewiseAffineOn.add {f g : E → F} {S : Set E}
    (hf : FinitePiecewiseAffineOn f S) (hg : FinitePiecewiseAffineOn g S) :
    FinitePiecewiseAffineOn (fun x => f x + g x) S :=
  (hf.prod_mk hg).postcomp
    (ContinuousLinearMap.fst ℝ F F + ContinuousLinearMap.snd ℝ F F).toContinuousAffineMap

/-- Differences use a common finite source subdivision, so
the original carrier is unchanged. See Hudson pp. 12--19 and
M76 derivation 270. -/
theorem FinitePiecewiseAffineOn.sub {f g : E → F} {S : Set E}
    (hf : FinitePiecewiseAffineOn f S) (hg : FinitePiecewiseAffineOn g S) :
    FinitePiecewiseAffineOn (fun x => f x - g x) S :=
  (hf.prod_mk hg).postcomp
    (ContinuousLinearMap.fst ℝ F F - ContinuousLinearMap.snd ℝ F F).toContinuousAffineMap

end Geometry
