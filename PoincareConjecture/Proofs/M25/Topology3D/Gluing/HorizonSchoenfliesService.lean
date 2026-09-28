import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.EssentialSphere.Euclidean
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SchoenfliesFromBall

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D

theorem schoenfliesService_from_main : SchoenfliesService := by
  intro ψ hψ δ hδ hδ1
  obtain ⟨e, he, hsource, htarget, hsymm⟩ := exists_collar_chart ψ hψ
  have hforward :
      ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E3) ∞ e e.source := by
    rw [hsource, he]
    exact hψ.1
  obtain ⟨F, hF⟩ := Poincare.exists_ambient_map_of_euclidean_sphere_collar
    e hforward hsymm zero_lt_one (by simpa using hsource)
  let B : BallNeighborhoodChart E3 E3 := {
    chart := F.toHomeomorph.toOpenPartialHomeomorph
    closedBall_subset_source := by simp
    smooth := F.contDiff.contDiffOn
    smooth_symm := F.symm.contDiff.contDiffOn }
  have hboundary : B.boundary = ψ '' (univ ×ˢ {0}) := by
    apply Set.Subset.antisymm
    · rintro y ⟨x, hx, rfl⟩
      let q : UnitTwoSphere := ⟨x, hx⟩
      refine ⟨(q, 0), ⟨mem_univ _, mem_singleton 0⟩, ?_⟩
      simpa [B, he] using (hF q).symm
    · rintro y ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩
      have ht0 : t = 0 := mem_singleton_iff.mp ht
      subst t
      refine ⟨(q : E3), q.property, ?_⟩
      simpa [B, he] using hF q
  exact schoenfliesData_of_ball ψ hψ B hboundary δ hδ hδ1

end PoincareConjecture.M25.Topology3D
