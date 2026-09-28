import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.SegmentLocality
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.NormalBall
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.ExponentialRays

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem exists_short_minimizing_geodesic_step
    (g : RiemannianMetric n M) (p q : M) {R : ℝ} (hR : 0 < R)
    (hcompact : IsCompact (closure (g.ball p R)))
    (hq : q ∈ g.ball p R) (hd : 0 < g.edist p q) :
    ∃ v : EuclideanSpace ℝ (Fin n), ∃ γ : ℝ → M,
      0 < g.tangentNorm p v ∧ g.tangentNorm p v < (g.edist p q).toReal ∧
      g.IsGeodesicOn γ (Ioo (-2 : ℝ) 2) ∧ γ 0 = p ∧
      HasDerivAt (fun t => extChartAt (𝓡 n) p (γ t)) v 0 ∧
      g.edist p q = ENNReal.ofReal (g.tangentNorm p v) + g.edist (γ 1) q := by
  let E := EuclideanSpace ℝ (Fin n)
  obtain ⟨e, h0, he0, he, he', hgauss, _, Γ, _, hΓ⟩ :=
    g.exists_exponential_chart_gauss p
  obtain ⟨r, hr, hsource, hdist⟩ :=
    g.exists_tangentBall_edist_eq_of_gauss p e h0 he0 he he' hgauss
  have hnorm : Continuous (fun v : E => g.tangentNorm p v) := by
    unfold tangentNorm
    exact Real.continuous_sqrt.comp
      ((continuous_const.clm_apply continuous_id).clm_apply continuous_id)
  have hV : {v : E | g.tangentNorm p v < r} ∈ 𝓝 0 :=
    (isOpen_lt hnorm continuous_const).mem_nhds (by simpa [tangentNorm] using hr)
  have hU : e '' {v : E | g.tangentNorm p v < r} ∈ 𝓝 p := by
    rw [← he0]
    have hset : {v : E | g.tangentNorm (e 0) v < r} =
        {v : E | g.tangentNorm p v < r} := by rw [he0]
    rw [hset]
    exact e.image_mem_nhds h0 hV
  have hfinite : g.edist p q ≠ ⊤ := ne_top_of_lt (hq.trans_le le_top)
  have hD : 0 < (g.edist p q).toReal := ENNReal.toReal_pos (ne_of_gt hd) hfinite
  obtain ⟨z, ⟨v, hv, hvz⟩, hzpos, hzsmall, hzadd⟩ :=
    g.exists_local_minimizing_step_of_precompact_ball p q hR hcompact hq hd hU hD
  have hedist : g.edist p z = ENNReal.ofReal (g.tangentNorm p v) := by
    rw [← hvz]
    exact hdist v hv
  have hvsource := hsource hv
  let γ := fun t => (extChartAt (𝓡 n) p).symm (Γ (v, t)).1
  have hgeod := g.geodesic_of_coordinate_exponential p
    (fun t => Γ (v, t)) v (hΓ v hvsource).1 (hΓ v hvsource).2.2
  have hγ1 : γ 1 = z := (hΓ v hvsource).2.1.trans hvz
  refine ⟨v, γ, ?_, ?_, hgeod.1, hgeod.2.1, hgeod.2.2, ?_⟩
  · exact ENNReal.ofReal_pos.mp (hedist ▸ hzpos)
  · exact (ENNReal.ofReal_lt_ofReal_iff hD).mp (hedist ▸ hzsmall)
  · rwa [hγ1, ← hedist]

end PoincareConjecture.RiemannianMetric
