import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Predecessors.Necks.Geometry.CentralSphere
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Predecessors.Analysis.Geometry.SmoothGraph
import Mathlib.Geometry.Manifold.Algebra.Structures

/-!
# Isotopy of two smooth height graphs inside one neck

Smooth graphs in neck coordinates are embedded spheres. Linear
interpolation of their heights stays in the neck and gives the sphere
isotopy used in Morgan--Tian Proposition A.11, pp. 503-504, and
Lemma A.13, p. 505. The assertion that an overlapping sphere is such
a graph is separate from this conditional construction.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M} (N : EpsilonNeck g)

/-- A smooth height graph inside the neck is a smooth embedded sphere
(the graph step of MT Proposition A.11, pp. 503-504). -/
theorem m25_coordinate_graph_isSmoothEmbedding (f : UnitTwoSphere → ℝ)
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    (hdom : ∀ q, f q ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞
      (fun q => N.coordinate_map (q, f q)) :=
  N.coordinatePartialHomeomorph.m25_isSmoothEmbedding_graph N.coordinate_map_smooth
    N.coordinate_inverse_smooth (RiemannianMetric.lineModelEquiv 2) f hf
      (fun q => ⟨mem_univ q, hdom q⟩)

/-- Two smooth height graphs in one neck are isotopic through smooth
embedded graphs in its carrier (MT A.11, pp. 503-504; A.13, p. 505). -/
theorem m25_coordinate_graphs_isotopic (f₀ f₁ : UnitTwoSphere → ℝ)
    (hf₀ : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f₀)
    (hf₁ : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f₁)
    (h₀ : ∀ q, f₀ q ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (h₁ : ∀ q, f₁ q ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    SmoothSphereIsotopicIn N.carrier
      (range (fun q => N.coordinate_map (q, f₀ q)))
      (range (fun q => N.coordinate_map (q, f₁ q))) := by
  let height := fun (z : ℝ × UnitTwoSphere) => (1 - z.1) * f₀ z.2 + z.1 * f₁ z.2
  have hsmooth : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞ height :=
    ((contMDiff_const.sub contMDiff_fst).mul (hf₀.comp contMDiff_snd)).add
      (contMDiff_fst.mul (hf₁.comp contMDiff_snd))
  have hheight (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (q : UnitTwoSphere) :
      height (t, q) ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    exact convex_Ioo _ _ (h₀ q) (h₁ q) (sub_nonneg.mpr ht.2) ht.1 (by ring)
  refine ⟨fun z => N.coordinate_map (z.2, height z), ?_, ?_, ?_, ?_⟩
  · exact N.coordinate_map_smooth.comp
      (contMDiff_snd.prodMk hsmooth).contMDiffOn
      (fun z hz => ⟨mem_univ _, hheight z.1 hz.1 z.2⟩)
  · intro t ht
    refine ⟨N.m25_coordinate_graph_isSmoothEmbedding (fun q => height (t, q))
      (((contMDiff_const.sub contMDiff_const).mul hf₀).add
        (contMDiff_const.mul hf₁)) (hheight t ht), ?_⟩
    rintro x ⟨q, rfl⟩
    exact N.coordinate_map_mem ⟨mem_univ _, hheight t ht q⟩
  · simp only [height, sub_zero, one_mul, zero_mul, add_zero]
  · simp only [height, sub_self, zero_mul, one_mul, zero_add]

end PoincareMT.EpsilonNeck
