import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.DistanceLower
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Overlap.GraphTransport








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Manifold
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M} (N : EpsilonNeck g)



theorem edist_center_lower_of_not_mem_closedCollar {r : ℝ}
    (hr : 0 < r) (hrN : r < N.epsilon⁻¹) {x : M} (hx : x ∉ N.closedCollar r) :
    ENNReal.ofReal (N.scale * Real.sqrt (1 - N.epsilon) * r) ≤
      g.edist N.center x := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hcenter := (N.mem_central_sphere_iff N.center).mp N.center_on_central_sphere
  by_contra h
  have hdist : Manifold.riemannianEDist (𝓡 3) N.center x <
      ENNReal.ofReal (N.scale * Real.sqrt (1 - N.epsilon) * r) := lt_of_not_ge h
  obtain ⟨γ, hγ0, hγ1, hγ, hlength, -, -⟩ :=
    exists_lt_locally_constant_of_riemannianEDist_lt hdist (show (0 : ℝ) < 1 by norm_num)
  have hleft : -N.epsilon⁻¹ < -r := neg_lt_neg hrN
  have hstart : γ 0 ∈ N.region (-r) r := by
    rw [hγ0]
    exact ⟨hcenter.1, hcenter.2 ▸ neg_lt_zero.mpr hr, hcenter.2 ▸ hr⟩
  have hout : γ 1 ∉ N.coordinate_map '' (univ ×ˢ Icc (-r) r) := by
    rw [hγ1]
    exact hx
  obtain ⟨t, ht, hcarrier, hboundary, -⟩ := N.exists_initial_segment_to_slab_boundary
    (show (0 : ℝ) ≤ 1 by norm_num) hleft hrN hγ.continuous.continuousOn hstart hout
  have hax := N.axial_displacement_le_pathELength ht.1.le hγ hcarrier
  have hvalue : |(N.coordinate_inverse (γ t)).2 -
      (N.coordinate_inverse (γ 0)).2| = r := by
    rw [hγ0, hcenter.2, sub_zero]
    rcases hboundary with hneg | hpos
    · rw [hneg, abs_neg, abs_of_pos hr]
    · rw [hpos, abs_of_pos hr]
  rw [hvalue] at hax
  have hmono : g.pathELength γ 0 t ≤ g.pathELength γ 0 1 :=
    Manifold.pathELength_mono le_rfl ht.2
  exact (not_lt_of_ge (hax.trans hmono)) hlength

end PoincareConjecture.EpsilonNeck
