import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Analysis.Geometry.SpatialJetsWithin

/-!
# Relative continuity of actual spatial jets

The actual spatial derivatives are continuous up to included time
endpoints because they restrict the continuous within derivatives by a
fixed multilinear operator. No ambient time derivative is required.
Reference: Morgan--Tian Proposition 5.14, pp. 90-91, and the
endpoint-spatial derivation under tasks/M28/partial-geometry.
-/

set_option autoImplicit false

open Set
open scoped ContDiff Topology

namespace PoincareMT.M28

/-- Spatial jets of a relatively smooth family are jointly continuous,
including every included time endpoint; Proposition 5.14, pp. 90-91. -/
theorem continuousOn_spatialJet_of_within
    {T E F : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {J : Set T} {U : Set E} {f : T × E → F}
    (hJ : UniqueDiffOn ℝ J) (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f (J ×ˢ U)) (m : ℕ) :
    ContinuousOn (fun z : T × E => iteratedFDeriv ℝ m (fun x => f (z.1, x)) z.2)
      (J ×ˢ U) := by
  let L := ContinuousMultilinearMap.compContinuousLinearMapL
    (F := F) (fun _ : Fin m => ContinuousLinearMap.inr ℝ T E)
  have hjet := hf.continuousOn_iteratedFDerivWithin (m := m)
    (by exact_mod_cast le_top) (hJ.prod hU.uniqueDiffOn)
  apply (L.continuous.comp_continuousOn hjet).congr
  intro z hz
  exact iteratedFDeriv_spatial_slice_eq_within hJ hU hf hz.1 hz.2
    (by exact_mod_cast le_top)

/-- At a fixed valid spatial point, every actual spatial derivative is a
continuous function of time within the actual time domain; Proposition
5.14, pp. 90-91. -/
theorem continuousOn_time_spatialJet_of_within
    {T E F : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {J : Set T} {U : Set E} {f : T × E → F}
    (hJ : UniqueDiffOn ℝ J) (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f (J ×ˢ U)) (m : ℕ) {x : E} (hx : x ∈ U) :
    ContinuousOn (fun t => iteratedFDeriv ℝ m (fun y => f (t, y)) x) J :=
  (continuousOn_spatialJet_of_within hJ hU hf m).comp
    (continuousOn_id.prodMk continuousOn_const) (fun _ ht => ⟨ht, hx⟩)

end PoincareMT.M28
