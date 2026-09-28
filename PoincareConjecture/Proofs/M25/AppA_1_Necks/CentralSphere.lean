import PoincareConjecture.Proofs.M25.AppA_1_Necks.Coordinates
import PoincareConjecture.Proofs.M25.Mathlib.SmoothSlice

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M} (N : EpsilonNeck g)

theorem coordinate_slice_isSmoothEmbedding {s : ℝ}
    (hs : s ∈ Set.Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞
      (fun q : UnitTwoSphere => N.coordinate_map (q, s)) :=
  N.coordinatePartialHomeomorph.m25_isSmoothEmbedding_slice N.coordinate_map_smooth
    N.coordinate_inverse_smooth (RiemannianMetric.lineModelEquiv 2) s
      (fun q => ⟨Set.mem_univ q, hs⟩)

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

end PoincareConjecture.EpsilonNeck
