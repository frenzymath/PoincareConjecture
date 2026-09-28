import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.Intersections.Coordinates
import PoincareConjecture.Proofs.M76.Dehn.OriginalFiniteIntersectionCover
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteChartPairAffineCover
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteChartFaceImage
import PoincareConjecture.Proofs.M76.Wall.CutDiskProjection











set_option autoImplicit false

open Set Geometry

namespace Geometry.OriginalPLTower

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

variable {M ι : Type*} [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ V2}
  {f : V2 → M} {r : M → ℝ} {C : Set M}






theorem FaceMotionData.exists_finite_original_pair_affine_cover
    {s t : Stage e S f r C} {step : Step s t}
    {K K₀ K₁ : SimplicialComplex ℝ V2} (hK : K.faces.Finite) (hK₀ : K₀ ≤ K)
    {face : Finset V2} (hface : face ∈ K.faces)
    (hsucc : K₁.space = K₀.space ∪ convexHull ℝ (face : Set V2))
    {j jfinal : V2 → t.Carrier} (hj : PolyhedralPLInCharts t.charts j K.space)
    (hji : InjOn j K.space) (hjfinal : PolyhedralPLInCharts t.charts jfinal K.space)
    (hfinal : InjOn jfinal K.space)
    {Q : OpenPartialHomeomorph t.Carrier V3}
    (hQ : ∀ k, (t.charts k).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (hjQ : MapsTo j (convexHull ℝ (face : Set V2)) Q.source)
    {B : OpenPartialHomeomorph s.Carrier V3}
    (hB : ∀ k, (s.charts k).symm.trans B ∈ piecewiseAffineGroupoid V3)
    (hval : ∀ z, Q z = B (step.projection (step.inclusion z)))
    (hmaps : MapsTo (step.projection ∘ step.inclusion) Q.source B.source)
    {J : SimplicialComplex ℝ V3} {U : K.faces → Set t.Carrier}
    {R Fmark : Set M} {boundary : Bool}
    (motion : FaceMotionData step K K₀ K₁ j Q B J U R Fmark boundary)
    (hold : EqOn jfinal j K₀.space)
    (hnext : EqOn jfinal (motion.ambient 1 ∘ j) K₁.space)
    (A : SimplicialComplex ℝ V2) (hA : A.space = Metric.sphere (0 : V2) 1)
    (old : K₀.faces)
    (hmarked : boundary = true → face ∈ A.faces ∧ old.val ∈ A.faces)
    (hcell : InjOn ((step.projection ∘ step.inclusion) ∘ jfinal)
      (convexHull ℝ (old.val : Set V2))) :
    ∃ T : Finset (AffineSubspace ℝ (V2 × V2)),
      (∀ L ∈ T, Module.finrank ℝ L.direction ≤ 1) ∧
      ∀ z : V2 × V2, z.1 ∈ convexHull ℝ (face : Set V2) → z.1 ∉ K₀.space →
        z.2 ∈ convexHull ℝ (old.val : Set V2) →
        step.projection (step.inclusion (jfinal z.1)) =
          step.projection (step.inclusion (jfinal z.2)) →
        ∃ L ∈ T, z ∈ L := by
  classical
  let p : V2 → s.Carrier := (step.projection ∘ step.inclusion) ∘ jfinal
  have hp : PolyhedralPLInCharts s.charts p K.space :=
    hjfinal.project step.chartIndex (step.projection.continuous.comp step.inclusion.continuous)
      step.chart_source (fun k x _ => congrFun (step.chart_forward k) x)
  let Kface := K.vertexSubcomplex (face : Set V2)
  let Kold := K.vertexSubcomplex (old.val : Set V2)
  have hKface : Kface.faces.Finite := K.vertexSubcomplex_finite (face : Set V2) hK
  have hKold : Kold.faces.Finite := K.vertexSubcomplex_finite (old.val : Set V2) hK
  have hKfaces : Kface.space = convexHull ℝ (face : Set V2) :=
    K.vertexSubcomplex_face_space hface
  have hKolds : Kold.space = convexHull ℝ (old.val : Set V2) :=
    K.vertexSubcomplex_face_space (hK₀ old.property)
  have hKfaceK : Kface.space ⊆ K.space :=
    SimplicialComplex.space_subset_of_le (K.vertexSubcomplex_le (face : Set V2))
  have hKoldK : Kold.space ⊆ K.space :=
    SimplicialComplex.space_subset_of_le (K.vertexSubcomplex_le (old.val : Set V2))
  have hpi : InjOn p Kold.space := hcell.mono hKolds.subset
  let common : Set V3 :=
    (motion.coordinates.map 1 '' motion.source.space \ motion.fixedSource.space) ∩
      (motion.targets old).space
  have hcommon : common ⊆ motion.support.space := by
    intro w hw
    exact ((motion.targets_space old).subset hw.2).2
  obtain ⟨T, hT, hcover⟩ :=
    motion.exists_finite_intersection_cover hK hK₀ hface hsucc hj hQ A hA old hmarked
  obtain ⟨Z, hZ, hZcover⟩ :=
    (hjfinal.restrict_finite Kface hKface hKfaceK).exists_finite_paired_chart_cover
      Kface hKface Kold hKold (hfinal.mono hKfaceK)
      (hp.restrict_finite Kold hKold hKoldK) hpi Q hQ B hB motion.support
      motion.support_finite motion.support_upper motion.support_lower
      hcommon T (fun L hL => (hT L hL).2.1)
      (fun w hw => hcover w hw.1.1 hw.1.2 hw.2)
  refine ⟨Z, hZ, ?_⟩
  intro z hx hxold hy hpair
  obtain ⟨hxQ, hyB, heq, _, hsource, hfree, htarget⟩ :=
    motion.original_pair_chart_coordinates hK₀ hface hsucc hji hjQ hval hmaps
      hold hnext old hx hxold hy hpair
  exact hZcover z.1 (hKfaces.symm.subset hx) z.2 (hKolds.symm.subset hy)
    hxQ hyB heq ⟨⟨hsource, hfree⟩, htarget⟩

end Geometry.OriginalPLTower
