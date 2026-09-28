import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.FaceData

set_option autoImplicit false

open Set Geometry

namespace Geometry.OriginalPLTower

variable {U E V M ι : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M E} {S : SimplicialComplex ℝ U}
  {f : U → M} {r : M → ℝ} {C : Set M}
  {s t : Stage e S f r C} {step : Step s t}
  {K K₀ K₁ : SimplicialComplex ℝ V} {j : V → t.Carrier}
  {Q : OpenPartialHomeomorph t.Carrier E}
  {B : OpenPartialHomeomorph s.Carrier E} {J : SimplicialComplex ℝ E}
  {U : K.faces → Set t.Carrier} {R Fmark : Set M} {boundary : Bool}

theorem MarkedSurfaceMotionData.targets_space_of_prefix_agreement
    (motion : MarkedSurfaceMotionData step K K₀ K₁ j Q B J U R Fmark boundary)
    {jfinal : V → t.Carrier} (heq : EqOn jfinal j K₀.space)
    (a : K₀.faces) :
    (motion.targets a).space = B ''
      (((step.projection ∘ step.inclusion) ∘ jfinal) ''
        convexHull ℝ (a.val : Set V) ∩ B.source) ∩ motion.support.space := by
  have himage : ((step.projection ∘ step.inclusion) ∘ jfinal) ''
      convexHull ℝ (a.val : Set V) =
      ((step.projection ∘ step.inclusion) ∘ j) '' convexHull ℝ (a.val : Set V) :=
    image_congr (fun x hx => congrArg (step.projection ∘ step.inclusion)
      (heq (K₀.convexHull_subset_space a.property hx)))
  rw [himage]
  exact motion.targets_space a

theorem MarkedSurfaceMotionData.coordinate_of_successor_agreement
    (motion : MarkedSurfaceMotionData step K K₀ K₁ j Q B J U R Fmark boundary)
    {jfinal : V → t.Carrier}
    (heq : EqOn jfinal (motion.ambient 1 ∘ j) K₁.space)
    {x : V} (hx : x ∈ K₁.space) (hxQ : j x ∈ Q.source)
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
