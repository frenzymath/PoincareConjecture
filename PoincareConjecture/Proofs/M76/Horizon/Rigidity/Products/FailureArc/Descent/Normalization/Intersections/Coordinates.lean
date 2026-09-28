import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.Intersections.Comparison
import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedSubcomplexCarriers











set_option autoImplicit false

open Set Geometry

namespace Geometry.OriginalPLTower

local notation "V3" => (Fin 3 → ℝ)

variable {U V M ι : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ U}
  {f : U → M} {r : M → ℝ} {C : Set M}





theorem MarkedSurfaceMotionData.original_pair_chart_coordinates
    {s t : Stage e S f r C} {step : Step s t}
    {K K₀ K₁ : SimplicialComplex ℝ V} (hK₀ : K₀ ≤ K)
    {face : Finset V} (hface : face ∈ K.faces)
    (hsucc : K₁.space = K₀.space ∪ convexHull ℝ (face : Set V))
    {j jfinal : V → t.Carrier} (hji : InjOn j K.space)
    {Q : OpenPartialHomeomorph t.Carrier V3}
    (hjQ : MapsTo j (convexHull ℝ (face : Set V)) Q.source)
    {B : OpenPartialHomeomorph s.Carrier V3}
    (hval : ∀ z, Q z = B (step.projection (step.inclusion z)))
    (hmaps : MapsTo (step.projection ∘ step.inclusion) Q.source B.source)
    {J : SimplicialComplex ℝ V3} {U : K.faces → Set t.Carrier}
    {R Fmark : Set M} {boundary : Bool}
    (motion : MarkedSurfaceMotionData step K K₀ K₁ j Q B J U R Fmark boundary)
    (hold : EqOn jfinal j K₀.space)
    (hnext : EqOn jfinal (motion.ambient 1 ∘ j) K₁.space)
    (old : K₀.faces) {x y : V}
    (hx : x ∈ convexHull ℝ (face : Set V)) (hxold : x ∉ K₀.space)
    (hy : y ∈ convexHull ℝ (old.val : Set V))
    (hpair : step.projection (step.inclusion (jfinal x)) =
      step.projection (step.inclusion (jfinal y))) :
    jfinal x ∈ Q.source ∧ step.projection (step.inclusion (jfinal y)) ∈ B.source ∧
      Q (jfinal x) = B (step.projection (step.inclusion (jfinal y))) ∧
      Q (jfinal x) ∈ motion.support.space ∧
      Q (jfinal x) ∈ motion.coordinates.map 1 '' motion.source.space ∧
      Q (jfinal x) ∉ motion.fixedSource.space ∧
      Q (jfinal x) ∈ (motion.targets old).space := by
  have hxnext : x ∈ K₁.space := hsucc.symm.subset (Or.inr hx)
  have hxQ := hjQ hx
  have hxC : Q (j x) ∈ motion.support.space :=
    interior_subset (motion.active_supported x hxnext hxold)
  have hvalue : Q (jfinal x) = motion.coordinates.map 1 (Q (j x)) :=
    motion.coordinate_of_successor_agreement hnext hxnext hxQ hxC
  have hwC : Q (jfinal x) ∈ motion.support.space := by
    rw [hvalue]
    exact (motion.coordinates.carrier 1).subset
      (mem_image_of_mem (motion.coordinates.map 1) hxC)
  have hfinalpoint : jfinal x = Q.symm (motion.coordinates.map 1 (Q (j x))) :=
    (hnext hxnext).trans (motion.chart_formula 1 hxQ)
  have hfinalQ : jfinal x ∈ Q.source := by
    rw [hfinalpoint]
    apply Q.map_target
    apply motion.support_upper
    rwa [← hvalue]
  have hyB : step.projection (step.inclusion (jfinal y)) ∈ B.source := by
    rw [← hpair]
    exact hmaps hfinalQ
  have hcommon : Q (jfinal x) = B (step.projection (step.inclusion (jfinal y))) := by
    rw [hval, hpair]
  refine ⟨hfinalQ, hyB, hcommon, hwC, ?_, ?_, ?_⟩
  · refine ⟨Q (j x), ?_, hvalue.symm⟩
    rw [motion.source_space]
    exact ⟨⟨j x, ⟨mem_image_of_mem j hxnext, hxQ⟩, rfl⟩, hxC⟩
  · intro hwfixed
    have hfix : motion.coordinates.map 1 (Q (jfinal x)) = Q (jfinal x) :=
      motion.coordinates.fixed_protected 1 (Q (jfinal x)) hwfixed
    have hsame : Q (j x) = Q (jfinal x) := (motion.coordinates.map 1).injective
      (hvalue.symm.trans hfix.symm)
    rw [motion.protected_space] at hwfixed
    obtain ⟨⟨v, ⟨⟨xold, hxold', rfl⟩, hjoldQ⟩, hcoord⟩, _⟩ := hwfixed
    have hjx : j x = j xold := Q.injOn hxQ hjoldQ (hsame.trans hcoord.symm)
    have hxx : x = xold := hji (K.convexHull_subset_space hface hx)
      (SimplicialComplex.space_subset_of_le hK₀ hxold') hjx
    exact hxold (hxx.symm ▸ hxold')
  · rw [motion.targets_space_of_prefix_agreement hold old]
    exact ⟨⟨step.projection (step.inclusion (jfinal y)),
      ⟨mem_image_of_mem ((step.projection ∘ step.inclusion) ∘ jfinal) hy, hyB⟩,
      hcommon.symm⟩, hwC⟩

end Geometry.OriginalPLTower
