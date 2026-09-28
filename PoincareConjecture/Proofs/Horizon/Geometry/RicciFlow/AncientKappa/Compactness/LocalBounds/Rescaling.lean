import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.LocalBounds.Volume
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.Rescaling.Closed










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture

variable {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]




theorem m23_exists_normalized_controlled_rescaling
    (P : M23NormalizedKappaCompactnessPredecessors) (K : AncientKappaSolution 3 M)
    (p x : M) {r ν : ℝ} (hr : 0 < r) (hν : 0 ≤ ν)
    (hx : x ∈ (K.flow.metric 0).ball p r)
    (hvolume : ENNReal.ofReal (ν * r ^ 3) ≤
      calibratedMetricVolume (K.flow.metric 0) ((K.flow.metric 0).ball p r)) :
    ∃ G : AncientKappaSolution 3 M, ∃ q : M, ∃ L : ℝ,
      G.kappa = K.kappa ∧ 0 < L ∧
      L = r * Real.sqrt ((K.flow.connection 0).scalarCurvature x) / 2 ∧
      (G.flow.connection 0).scalarCurvature q = 1 ∧
      (∀ t : ℝ, t ≤ 0 → ∀ y ∈ (G.flow.metric 0).ball q L,
        |(G.flow.connection t).curvatureTensorNorm y| ≤ 4) ∧
      ∀ a : ℝ, 0 < a → a ≤ L →
        ENNReal.ofReal ((ν / 27) * a ^ 3) ≤
          calibratedMetricVolume (G.flow.metric 0) ((G.flow.metric 0).ball q a) := by
  obtain ⟨q, s, _, hs, hsr, _, hscale, hbound, hvol⟩ :=
    m23_exists_backward_controlled_point_with_volume P K p x hr hν hx hvolume
  let Q := (K.flow.connection 0).scalarCurvature q
  have hQ : 0 < Q := P.scalar_pos M K 0 le_rfl q
  have hsqrt : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  obtain ⟨R⟩ := P.ordinary_rescaling M closedAncientInterval K.flow Q hQ 0
  let G := K.closedRescale hQ (le_refl 0) R
  let L := Real.sqrt Q * s
  have hL : 0 < L := mul_pos hsqrt hs
  have hball : (K.flow.metric 0).ball q s = (G.flow.metric 0).ball q L := by
    simpa only [zero_div, add_zero, Diffeomorph.coe_refl, id_eq, image_id'] using
      (K.closedRescale_metric_calculus hQ (le_refl 0) R 0).ball_image q s
  refine ⟨G, q, L, rfl, hL, ?_, ?_, ?_, ?_⟩
  · exact (mul_comm _ _).trans hscale
  · rw [K.closedRescale_scalar]
    rw [show (0 : ℝ) + 0 / Q = 0 by simp]
    exact div_self hQ.ne'
  · intro t ht y hy
    change |((K.closedRescale hQ (le_refl 0) R).flow.connection t).curvatureTensorNorm y| ≤ 4
    rw [K.closedRescale_curvature_norm, abs_div, abs_of_pos hQ]
    apply (div_le_iff₀ hQ).mpr
    rw [show (0 : ℝ) + t / Q = t / Q by simp]
    exact hbound (t / Q) (div_nonpos_of_nonpos_of_nonneg ht hQ.le) y (hball.symm ▸ hy)
  · intro a ha haL
    have ha' : 0 < a / Real.sqrt Q := div_pos ha hsqrt
    have has : a / Real.sqrt Q ≤ s := (div_le_iff₀ hsqrt).mpr (by
      simpa only [L, mul_comm] using haL)
    have hv := hvol (a / Real.sqrt Q) ha' (by linarith)
    have hscaled := (K.closedRescale_ball_volume_lower_bound_iff
      hQ (le_refl 0) R q (a / Real.sqrt Q) (ν / 27)).mpr hv
    simpa only [mul_div_cancel₀ a hsqrt.ne'] using hscaled

end PoincareConjecture
