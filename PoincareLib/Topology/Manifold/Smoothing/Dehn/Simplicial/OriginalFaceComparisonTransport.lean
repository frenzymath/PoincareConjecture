import PoincareLib.Topology.Manifold.Smoothing.Dehn.Simplicial.OriginalFaceMotionData

/-!
# Retain the actual face comparison at the final endpoint

Whole-prefix agreement makes each entire original lower comparison
image literally unchanged. Whole-successor agreement carries the
actual coordinate motion formula to the final disk at every valid
source point in its support. No perturbation stability is used.
See Hudson1969, Lemma4.6, and Dehn032, sections4--7.
-/

set_option autoImplicit false

open Set Geometry

namespace Geometry.OriginalPLTower

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

variable {M ι : Type*} [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ V2}
  {f : V2 → M} {r : M → ℝ} {C : Set M}
  {s t : Stage e S f r C} {step : Step s t}
  {K K₀ K₁ : SimplicialComplex ℝ V2} {j : V2 → t.Carrier}
  {Q : OpenPartialHomeomorph t.Carrier V3}
  {B : OpenPartialHomeomorph s.Carrier V3} {J : SimplicialComplex ℝ V3}
  {U : K.faces → Set t.Carrier} {R Fmark : Set M} {boundary : Bool}

/-- Whole-prefix agreement retains the complete clipped image of
every unchanged lower source face, including its chart-domain
restriction. See Dehn032, section4, and the finite-assembly
supplement, section5. -/
theorem FaceMotionData.targets_space_of_prefix_agreement
    (motion : FaceMotionData step K K₀ K₁ j Q B J U R Fmark boundary)
    {jfinal : V2 → t.Carrier} (heq : EqOn jfinal j K₀.space)
    (a : K₀.faces) :
    (motion.targets a).space = B ''
      (((step.projection ∘ step.inclusion) ∘ jfinal) ''
        convexHull ℝ (a.val : Set V2) ∩ B.source) ∩ motion.support.space := by
  have himage : ((step.projection ∘ step.inclusion) ∘ jfinal) ''
      convexHull ℝ (a.val : Set V2) =
      ((step.projection ∘ step.inclusion) ∘ j) '' convexHull ℝ (a.val : Set V2) :=
    image_congr (fun x hx => congrArg (step.projection ∘ step.inclusion)
      (heq (K₀.convexHull_subset_space a.property hx)))
  rw [himage]
  exact motion.targets_space a

/-- At a valid original source point in the actual support,
whole-successor agreement retains the literal produced coordinate
motion in the final disk. All chart inverse identities are used
inside their full domains. See Dehn032, sections4--7. -/
theorem FaceMotionData.coordinate_of_successor_agreement
    (motion : FaceMotionData step K K₀ K₁ j Q B J U R Fmark boundary)
    {jfinal : V2 → t.Carrier}
    (heq : EqOn jfinal (motion.ambient 1 ∘ j) K₁.space)
    {x : V2} (hx : x ∈ K₁.space) (hxQ : j x ∈ Q.source)
    (hxC : Q (j x) ∈ motion.support.space) :
    Q (jfinal x) = motion.coordinates.map 1 (Q (j x)) := by
  have hinside : motion.coordinates.map 1 (Q (j x)) ∈ motion.support.space :=
    (motion.coordinates.carrier 1).subset
      (mem_image_of_mem (motion.coordinates.map 1) hxC)
  rw [heq hx]
  change Q (motion.ambient 1 (j x)) = motion.coordinates.map 1 (Q (j x))
  rw [motion.chart_formula 1 hxQ]
  exact Q.right_inv (motion.support_upper hinside)

end Geometry.OriginalPLTower
