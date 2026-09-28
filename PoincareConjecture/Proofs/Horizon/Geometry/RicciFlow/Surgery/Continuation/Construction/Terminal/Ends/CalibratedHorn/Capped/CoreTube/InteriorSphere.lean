import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.NeckGeometry
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.CollarDistance

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Manifold
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}

theorem edist_lower_of_not_mem_coordinate_slab (N : EpsilonNeck g)
    {a b d : ℝ} (ha : -N.epsilon⁻¹ < a) (hb : b < N.epsilon⁻¹)
    {p x : M} (hp : p ∈ N.region a b)
    (hda : d ≤ (N.coordinate_inverse p).2 - a)
    (hdb : d ≤ b - (N.coordinate_inverse p).2)
    (hx : x ∉ N.coordinate_map '' (univ ×ˢ Icc a b)) :
    ENNReal.ofReal (N.scale * Real.sqrt (1 - N.epsilon) * d) ≤ g.edist p x := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  by_contra h
  have hdist : Manifold.riemannianEDist (𝓡 3) p x <
      ENNReal.ofReal (N.scale * Real.sqrt (1 - N.epsilon) * d) := lt_of_not_ge h
  obtain ⟨γ, hγ0, hγ1, hγ, hlength, -, -⟩ :=
    exists_lt_locally_constant_of_riemannianEDist_lt hdist (show (0 : ℝ) < 1 by norm_num)
  obtain ⟨t, ht, hcarrier, hboundary, -⟩ := N.exists_initial_segment_to_slab_boundary
    (show (0 : ℝ) ≤ 1 by norm_num) ha hb hγ.continuous.continuousOn
      (hγ0.symm ▸ hp) (hγ1.symm ▸ hx)
  have hvalue : d ≤ |(N.coordinate_inverse (γ t)).2 -
      (N.coordinate_inverse (γ 0)).2| := by
    rw [hγ0]
    rcases hboundary with hleft | hright
    · rw [hleft, abs_of_neg (by linarith [hp.2.1])]
      linarith
    · rw [hright, abs_of_pos (by linarith [hp.2.2])]
      exact hdb
  have hax := (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left hvalue (mul_nonneg N.scale_pos.le (Real.sqrt_nonneg _)))).trans
      (N.axial_displacement_le_pathELength ht.1.le hγ hcarrier)
  have hmono : g.pathELength γ 0 t ≤ g.pathELength γ 0 1 :=
    Manifold.pathELength_mono le_rfl ht.2
  exact (not_lt_of_ge (hax.trans hmono)) hlength

end PoincareConjecture.EpsilonNeck
