import PoincareConjecture.Proofs.M47.TerminalSourceChartsBuffers
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.TimeTranslation
import PoincareConjecture.Statements.Ch04.CurvatureTheory








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)



theorem terminalSourceJets_curvature (P : RicciFlowCurvatureTheory.{u})
    {τ R H ρ : ℝ} (hτ : 0 < τ) (hH : 0 < H) (hρ : 0 < ρ) (hρR : 2 * ρ < R)
    (hsmall : ∀ s : ℝ, |s| ≤ 2 * ρ →
      (H * s ^ 2) * Real.exp (max 1 (H * s ^ 2)) ≤ 3) (j : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
      [IsManifold (𝓡 3) ∞ M] [T2Space M] [SecondCountableTopology M],
      ∀ (F : RicciFlow 3 M (Icc (-τ) 0)) (C : TerminalSourceChart (F.metric 0) R),
      (∀ t ∈ Icc (-τ) 0, ∀ y ∈ C.chart '' Metric.ball 0 R,
        (F.connection t).curvatureTensorNorm y ≤ H) →
      ∀ t ∈ Icc (-(τ / 2)) 0, ∀ x ∈ Metric.ball 0 (3 * ρ / 2),
        (F.connection t).curvatureDerivativeNorm j (C.chart x) ≤ D := by
  let a := terminalSourceLower H τ
  let r := terminalSourceShiRadius a ρ
  have ha : 0 < a := terminalSourceLower_pos H τ
  have hr : 0 < r := terminalSourceShiRadius_pos ha hρ
  obtain ⟨D, hD, hShi⟩ := P.local_derivative_estimates 3 j H (H * τ) r
    hH (mul_pos hH hτ) hr
  refine ⟨D / (τ / 2) ^ ((j : ℝ) / 2), by positivity, ?_⟩
  intro M _ _ _ _ _ F C hcurv t ht x hx
  have hcompact := terminalSourceCharts_compact_ball (F.metric (-τ)) C.chart C.source
    hρ hρR ha
    (fun z hz v => (C.closed_bounds hτ hH.le F hρR hsmall hcurv
      ⟨le_rfl, by linarith⟩ hz v).1) hx
  have hmap : (fun s : ℝ => s + -τ) '' Icc 0 τ ⊆ Icc (-τ) 0 := by
    rintro _ ⟨s, hs, rfl⟩
    constructor <;> linarith [hs.1, hs.2]
  have hnontrivial : (Icc (0 : ℝ) τ).Nontrivial :=
    ⟨0, ⟨le_rfl, hτ.le⟩, τ, ⟨hτ.le, le_rfl⟩, hτ.ne⟩
  let G := F.translate (-τ) hmap ordConnected_Icc hnontrivial
  have htime : τ ≤ (H * τ) / H := by rw [mul_div_cancel_left₀ τ hH.ne']
  have hG0 : G.metric 0 = F.metric (-τ) := by
    change F.metric (0 + -τ) = F.metric (-τ)
    rw [zero_add]
  have hGc : IsCompact (closure ((G.metric 0).ball (C.chart x) r)) := by
    rw [hG0]
    exact hcompact.1
  have hGcurv : ∀ s ∈ Icc 0 τ, ∀ y ∈ (G.metric 0).ball (C.chart x) r,
      (G.connection s).curvatureTensorNorm y ≤ H := by
    intro s hs y hy
    rw [hG0] at hy
    exact hcurv (s + -τ) (hmap ⟨s, hs, rfl⟩) y (hcompact.2 hy)
  have hcentre : C.chart x ∈ (G.metric 0).ball (C.chart x) (r / 2) := by
    change (G.metric 0).edist (C.chart x) (C.chart x) < ENNReal.ofReal (r / 2)
    rw [M36.metric_edist_self]
    exact ENNReal.ofReal_pos.mpr (by positivity)
  have hs : t + τ ∈ Ioc 0 τ := by constructor <;> linarith [ht.1, ht.2]
  have hb := hShi M τ hτ htime G (C.chart x) hGc hGcurv (t + τ) hs _ hcentre
  change (F.connection (t + τ + -τ)).curvatureDerivativeNorm j (C.chart x) ≤ _ at hb
  rw [add_neg_cancel_right] at hb
  apply hb.trans (div_le_div_of_nonneg_left hD.le (by positivity) ?_)
  exact Real.rpow_le_rpow (by positivity) (by linarith [ht.1]) (by positivity)

end PoincareConjecture.M47
