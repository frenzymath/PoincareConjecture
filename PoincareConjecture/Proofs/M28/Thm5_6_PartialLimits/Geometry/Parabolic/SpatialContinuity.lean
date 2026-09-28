import PoincareConjecture.Proofs.M28.Mathlib.SpatialJetsWithin











set_option autoImplicit false

open Set
open scoped ContDiff Topology

namespace PoincareConjecture.M28



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

end PoincareConjecture.M28
