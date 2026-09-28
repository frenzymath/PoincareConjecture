import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.MetricSpace.Lipschitz










set_option autoImplicit false

open Set Filter
open scoped Topology

namespace PoincareConjecture.M63





theorem continuous_uncurry_of_dense_bounded_lipschitz
    {P E F : Type*} [TopologicalSpace P] [NormedAddCommGroup E] [NormedAddCommGroup F]
    (G : P → E → F) (s : Set E) (hs : Dense s)
    (hcore : ∀ u ∈ s, Continuous (fun p => G p u))
    (hLip : ∀ R : ℝ, 0 < R → ∃ K : NNReal,
      ∀ p, LipschitzOnWith K (G p) {u | ‖u‖ ≤ R}) :
    Continuous (fun z : P × E => G z.1 z.2) := by
  have hequi : Equicontinuous G := by
    intro u
    rw [Metric.equicontinuousAt_iff_right]
    intro ε hε
    obtain ⟨K, hK⟩ := hLip (‖u‖ + 1) (by positivity)
    have hb : ∀ᶠ v : E in 𝓝 u, ‖v‖ ≤ ‖u‖ + 1 :=
      continuous_norm.continuousAt.preimage_mem_nhds (Iic_mem_nhds (by linarith))
    have hz : Tendsto (fun v : E => (K : ℝ) * dist u v) (𝓝 u) (𝓝 0) := by
      simpa only [id_eq, dist_self, mul_zero] using
        (((continuous_const : Continuous (fun _ : E => u)).dist continuous_id).const_mul
          (K : ℝ)).tendsto u
    filter_upwards [hb, hz.eventually (gt_mem_nhds hε)] with v hv hdist p
    exact lt_of_le_of_lt ((hK p).dist_le_mul u (by dsimp; linarith) v hv) hdist
  have hparam (u : E) : Continuous (fun p => G p u) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    have hc : IsClosed {v | Tendsto (fun q => G q v) (𝓝 p) (𝓝 (G p v))} :=
      hequi.isClosed_setOfPred_tendsto (hequi.continuous p)
    exact (closure_minimal (fun v hv => (hcore v hv).continuousAt) hc) (hs u)
  apply continuous_iff_continuousAt.mpr
  rintro ⟨p, u⟩
  obtain ⟨K, hK⟩ := hLip (‖u‖ + 1) (by positivity)
  have hb : ∀ᶠ z : P × E in 𝓝 (p, u), ‖z.2‖ ≤ ‖u‖ + 1 :=
    continuous_snd.norm.continuousAt.preimage_mem_nhds (Iic_mem_nhds (by linarith))
  have hbound : ∀ᶠ z : P × E in 𝓝 (p, u),
      dist (G z.1 z.2) (G p u) ≤
        (K : ℝ) * dist z.2 u + dist (G z.1 u) (G p u) := by
    filter_upwards [hb] with z hz
    exact (dist_triangle _ (G z.1 u) _).trans
      (add_le_add ((hK z.1).dist_le_mul z.2 hz u (by dsimp; linarith)) le_rfl)
  have hc : Continuous (fun z : P × E =>
      (K : ℝ) * dist z.2 u + dist (G z.1 u) (G p u)) := by
    exact ((continuous_snd.dist continuous_const).const_mul _).add
      ((hparam u).comp continuous_fst |>.dist continuous_const)
  change Tendsto _ (𝓝 (p, u)) (𝓝 _)
  rw [tendsto_iff_dist_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun _ => dist_nonneg)) hbound
  simpa only [dist_self, mul_zero, add_zero] using hc.tendsto (p, u)

end PoincareConjecture.M63
