import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.Intersections.FiniteEdges
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.Intersections.Comparison











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






theorem MarkedSurfaceMotionData.finite_original_edge_pairs
    {s t : Stage e S f r C} {step : Step s t}
    {K K₀ K₁ : SimplicialComplex ℝ V} (hK : K.faces.Finite) (hK₀ : K₀ ≤ K)
    {face : Finset V} (hface : face ∈ K.faces)
    (hsucc : K₁.space = K₀.space ∪ convexHull ℝ (face : Set V))
    {j jfinal : V → t.Carrier} (hj : PolyhedralPLInCharts t.charts j K.space)
    (hji : InjOn j K.space) (hfinal : InjOn jfinal K.space)
    {Q : OpenPartialHomeomorph t.Carrier V3}
    (hQ : ∀ k, (t.charts k).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (hjQ : MapsTo j (convexHull ℝ (face : Set V)) Q.source)
    {B : OpenPartialHomeomorph s.Carrier V3}
    (hval : ∀ z, Q z = B (step.projection (step.inclusion z)))
    (hmaps : MapsTo (step.projection ∘ step.inclusion) Q.source B.source)
    {J : SimplicialComplex ℝ V3} {U : K.faces → Set t.Carrier}
    {R Fmark : Set M} {boundary : Bool}
    (motion : MarkedSurfaceMotionData step K K₀ K₁ j Q B J U R Fmark boundary)
    (hold : EqOn jfinal j K₀.space)
    (hnext : EqOn jfinal (motion.ambient 1 ∘ j) K₁.space)
    (hKdim : ∀ c ∈ K.faces, c.card ≤ 3)
    (A : SimplicialComplex ℝ V) (hAdim : ∀ c ∈ A.faces, c.card ≤ 2)
    (old : K₀.faces)
    (hmarked : boundary = true → face ∈ A.faces ∧ old.val ∈ A.faces)
    (hsmall : boundary = true ∨ face.card ≤ 2 ∨ old.val.card ≤ 2)
    (hcell : InjOn ((step.projection ∘ step.inclusion) ∘ jfinal)
      (convexHull ℝ (old.val : Set V))) :
    {z : V × V | z.1 ∈ convexHull ℝ (face : Set V) ∧ z.1 ∉ K₀.space ∧
      z.2 ∈ convexHull ℝ (old.val : Set V) ∧
      step.projection (step.inclusion (jfinal z.1)) =
        step.projection (step.inclusion (jfinal z.2))}.Finite := by
  let pairs : Set (V × V) :=
    {z | z.1 ∈ convexHull ℝ (face : Set V) ∧ z.1 ∉ K₀.space ∧
      z.2 ∈ convexHull ℝ (old.val : Set V) ∧
      step.projection (step.inclusion (jfinal z.1)) =
        step.projection (step.inclusion (jfinal z.2))}
  let value (z : V × V) : V3 := Q (jfinal z.1)
  have hcoords (z : V × V) (hz : z ∈ pairs) : jfinal z.1 ∈ Q.source ∧
      value z ∈ motion.coordinates.map 1 '' motion.source.space ∧
      value z ∉ motion.fixedSource.space ∧ value z ∈ (motion.targets old).space := by
    have hxnext : z.1 ∈ K₁.space := hsucc.symm.subset (Or.inr hz.1)
    have hxQ := hjQ hz.1
    have hxC : Q (j z.1) ∈ motion.support.space :=
      interior_subset (motion.active_supported z.1 hxnext hz.2.1)
    have hvalue : value z = motion.coordinates.map 1 (Q (j z.1)) :=
      motion.coordinate_of_successor_agreement hnext hxnext hxQ hxC
    have hwC : value z ∈ motion.support.space := by
      rw [hvalue]
      exact (motion.coordinates.carrier 1).subset
        (mem_image_of_mem (motion.coordinates.map 1) hxC)
    have hfinalpoint : jfinal z.1 = Q.symm (motion.coordinates.map 1 (Q (j z.1))) :=
      (hnext hxnext).trans (motion.chart_formula 1 hxQ)
    have hfinalQ : jfinal z.1 ∈ Q.source := by
      rw [hfinalpoint]
      apply Q.map_target
      apply motion.support_upper
      rwa [← hvalue]
    refine ⟨hfinalQ, ?_, ?_, ?_⟩
    · refine ⟨Q (j z.1), ?_, hvalue.symm⟩
      rw [motion.source_space]
      exact ⟨⟨j z.1, ⟨mem_image_of_mem j hxnext, hxQ⟩, rfl⟩, hxC⟩
    · intro hwfixed
      have hfix : motion.coordinates.map 1 (value z) = value z :=
        motion.coordinates.fixed_protected 1 (value z) hwfixed
      have hsame : Q (j z.1) = value z := (motion.coordinates.map 1).injective
        (hvalue.symm.trans hfix.symm)
      rw [motion.protected_space] at hwfixed
      obtain ⟨⟨v, ⟨⟨xold, hxold, rfl⟩, hjoldQ⟩, hcoord⟩, _⟩ := hwfixed
      have hjx : j z.1 = j xold := Q.injOn hxQ hjoldQ (hsame.trans hcoord.symm)
      have hxx : z.1 = xold := hji (K.convexHull_subset_space hface hz.1)
        (SimplicialComplex.space_subset_of_le hK₀ hxold) hjx
      exact hz.2.1 (hxx.symm ▸ hxold)
    · have hcommon : value z = B (step.projection (step.inclusion (jfinal z.2))) := by
        change Q (jfinal z.1) = B (step.projection (step.inclusion (jfinal z.2)))
        rw [hval, hz.2.2.2]
      rw [motion.targets_space_of_prefix_agreement hold old]
      refine ⟨⟨step.projection (step.inclusion (jfinal z.2)), ?_, hcommon.symm⟩, hwC⟩
      refine ⟨mem_image_of_mem ((step.projection ∘ step.inclusion) ∘ jfinal) hz.2.2.1, ?_⟩
      have hyB := hmaps hfinalQ
      change step.projection (step.inclusion (jfinal z.1)) ∈ B.source at hyB
      rwa [hz.2.2.2] at hyB
  have hinj : InjOn value pairs := by
    intro z hz w hw hzw
    have hx : z.1 = w.1 := hfinal (K.convexHull_subset_space hface hz.1)
      (K.convexHull_subset_space hface hw.1)
      (Q.injOn (hcoords z hz).1 (hcoords w hw).1 hzw)
    have hy : z.2 = w.2 := hcell hz.2.2.1 hw.2.2.1
      (hz.2.2.2.symm.trans ((congrArg
        (fun x => step.projection (step.inclusion (jfinal x))) hx).trans hw.2.2.2))
    exact Prod.ext hx hy
  have hfinite := motion.finite_edge_comparison_intersection
    hK hK₀ hface hsucc hj hQ hKdim A hAdim old hmarked hsmall
  exact hfinite.of_injOn (fun z hz => (hcoords z hz).2) hinj

end Geometry.OriginalPLTower
