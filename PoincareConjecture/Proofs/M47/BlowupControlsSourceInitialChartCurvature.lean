import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialChartBounds
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.TimeTranslation
import PoincareConjecture.Statements.Ch04.CurvatureTheory










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)



theorem source_initial_chart_curvature (P : RicciFlowCurvatureTheory.{u})
    {tau R K rho a b : ℝ} (htau : 0 < tau) (hK : 0 < K)
    (hrho : 0 < rho) (hrhoR : 2 * rho < R) (ha : 0 < a) (j : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
      [IsManifold (𝓡 3) ∞ M] [T2Space M] [SecondCountableTopology M],
      ∀ (F : RicciFlow 3 M (Icc (-tau) 0))
        (Phi : PartialDiffeomorph (𝓡 3) (𝓡 3) E M ∞),
      Phi.source = Metric.ball 0 R →
      (∀ s ∈ Icc (-tau) 0, ∀ y ∈ Phi '' Metric.ball 0 R,
        (F.connection s).curvatureTensorNorm y ≤ K) →
      (∀ x ∈ Metric.closedBall (0 : E) (2 * rho), ∀ v,
        a * ‖v‖ ^ 2 ≤ (F.metric 0).pullbackCoefficients Phi x v v ∧
          (F.metric 0).pullbackCoefficients Phi x v v ≤ b * ‖v‖ ^ 2) →
      ∀ s ∈ Icc (-(tau / 2)) 0, ∀ x ∈ Metric.ball 0 (3 * rho / 2),
        (F.connection s).curvatureDerivativeNorm j (Phi x) ≤ D := by
  let lower := a * Real.exp (-54 * K * tau)
  let r := terminalSourceShiRadius lower rho
  have hlower : 0 < lower := mul_pos ha (Real.exp_pos _)
  have hr : 0 < r := terminalSourceShiRadius_pos hlower hrho
  obtain ⟨D, hD, hShi⟩ := P.local_derivative_estimates 3 j K (K * tau) r
    hK (mul_pos hK htau) hr
  refine ⟨D / (tau / 2) ^ ((j : ℝ) / 2), by positivity, ?_⟩
  intro M _ _ _ _ _ F Phi hsource hcurv hterminal s hs x hx
  have hcompact := terminalSourceCharts_compact_ball (F.metric (-tau)) Phi hsource
    hrho hrhoR hlower
    (fun z hz v => (source_initial_chart_closed_bounds htau hK.le hrhoR F Phi
      hcurv hterminal ⟨le_rfl, by linarith only [htau]⟩ hz v).1) hx
  have hmap : (fun t : ℝ => t + -tau) '' Icc 0 tau ⊆ Icc (-tau) 0 := by
    rintro _ ⟨t, ht, rfl⟩
    constructor <;> linarith only [ht.1, ht.2]
  have hnontrivial : (Icc (0 : ℝ) tau).Nontrivial :=
    ⟨0, ⟨le_rfl, htau.le⟩, tau, ⟨htau.le, le_rfl⟩, htau.ne⟩
  let G := F.translate (-tau) hmap ordConnected_Icc hnontrivial
  have htime : tau ≤ (K * tau) / K := by rw [mul_div_cancel_left₀ tau hK.ne']
  have hG0 : G.metric 0 = F.metric (-tau) := by
    change F.metric (0 + -tau) = F.metric (-tau)
    rw [zero_add]
  have hGc : IsCompact (closure ((G.metric 0).ball (Phi x) r)) := by
    rw [hG0]
    exact hcompact.1
  have hGcurv : ∀ t ∈ Icc 0 tau, ∀ y ∈ (G.metric 0).ball (Phi x) r,
      (G.connection t).curvatureTensorNorm y ≤ K := by
    intro t ht y hy
    rw [hG0] at hy
    exact hcurv (t + -tau) (hmap ⟨t, ht, rfl⟩) y (hcompact.2 hy)
  have hcentre : Phi x ∈ (G.metric 0).ball (Phi x) (r / 2) := by
    change (G.metric 0).edist (Phi x) (Phi x) < ENNReal.ofReal (r / 2)
    rw [M36.metric_edist_self]
    exact ENNReal.ofReal_pos.mpr (by positivity)
  have ht : s + tau ∈ Ioc 0 tau := by
    constructor <;> linarith only [hs.1, hs.2, htau]
  have hb := hShi M tau htau htime G (Phi x) hGc hGcurv (s + tau) ht _ hcentre
  change (F.connection (s + tau + -tau)).curvatureDerivativeNorm j (Phi x) ≤ _ at hb
  rw [add_neg_cancel_right] at hb
  apply hb.trans (div_le_div_of_nonneg_left hD.le (by positivity) ?_)
  exact Real.rpow_le_rpow (by positivity) (by linarith only [hs.1]) (by positivity)

end PoincareConjecture.M47
