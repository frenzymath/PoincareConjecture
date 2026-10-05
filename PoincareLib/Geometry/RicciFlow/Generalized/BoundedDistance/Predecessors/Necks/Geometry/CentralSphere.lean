import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Predecessors.Necks.Coordinates.Coordinates
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Predecessors.Analysis.Geometry.SmoothSlice

/-!
# Embedded neck slices and the constant central-sphere isotopy

The actual coordinate spheres of Morgan--Tian Definition 2.18, p. 31, are
smoothly embedded. The constant central-sphere isotopy supplies the one-neck
base case of Lemma A.13, p. 505.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M} (N : EpsilonNeck g)

/-- Every coordinate slice inside the neck is a smooth embedded sphere
(Def. 2.18, p. 31; the product slices used in A.13, p. 505). -/
theorem coordinate_slice_isSmoothEmbedding {s : ℝ}
    (hs : s ∈ Set.Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞
      (fun q : UnitTwoSphere => N.coordinate_map (q, s)) :=
  N.coordinatePartialHomeomorph.m25_isSmoothEmbedding_slice N.coordinate_map_smooth
    N.coordinate_inverse_smooth (RiemannianMetric.lineModelEquiv 2) s
      (fun q => ⟨Set.mem_univ q, hs⟩)

/-- The zero coordinate slice has exactly the frozen central sphere as its
range (Def. 2.18, p. 31). -/
theorem coordinate_zero_range :
    Set.range (fun q : UnitTwoSphere => N.coordinate_map (q, 0)) = N.central_sphere := by
  rw [N.central_sphere_eq]
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨(q, 0), ⟨Set.mem_univ _, rfl⟩, rfl⟩
  · rintro ⟨⟨q, t⟩, ⟨_, ht⟩, hx⟩
    have ht' : t = 0 := ht
    subst t
    exact ⟨q, hx⟩

/-- A neck's central sphere is isotopic to itself through actual smooth
embeddings in the carrier (one-neck case of A.13, p. 505). -/
theorem m25_central_sphere_isotopic_self :
    SmoothSphereIsotopicIn N.carrier N.central_sphere N.central_sphere := by
  have h := N.coordinate_slice_isSmoothEmbedding N.zero_mem_interval
  refine ⟨fun z => N.coordinate_map (z.2, 0),
    (h.contMDiff.comp contMDiff_snd).contMDiffOn, ?_,
    N.coordinate_zero_range, N.coordinate_zero_range⟩
  intro t ht
  refine ⟨h, ?_⟩
  rw [N.coordinate_zero_range]
  exact N.central_sphere_subset

end PoincareMT.EpsilonNeck
