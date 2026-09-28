import PoincareConjecture.Proofs.M47.TerminalSourceChartsBuffers
import PoincareConjecture.Proofs.M47.TerminalSourceJetsCurvature









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)



theorem limitFinite_chart_closed_bounds
    {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] {τ R K ρ a0 b0 : ℝ}
    (hτ : 0 < τ) (hK : 0 ≤ K) (hρR : 2 * ρ < R)
    (F : RicciFlow 3 M (Icc (-τ) 0))
    (Φ : PartialDiffeomorph (𝓡 3) (𝓡 3) E M ∞)
    (hcurv : ∀ t ∈ Icc (-τ) 0, ∀ y ∈ Φ '' Metric.ball 0 R,
      (F.connection t).curvatureTensorNorm y ≤ K)
    (hterminal : ∀ x ∈ Metric.closedBall 0 (2 * ρ), ∀ v : E,
      a0 * ‖v‖ ^ 2 ≤ (F.metric 0).pullbackCoefficients Φ x v v ∧
        (F.metric 0).pullbackCoefficients Φ x v v ≤ b0 * ‖v‖ ^ 2)
    {t : ℝ} (ht : t ∈ Icc (-τ) 0) {x : E}
    (hx : x ∈ Metric.closedBall 0 (2 * ρ)) (v : E) :
    (a0 * Real.exp (-54 * K * τ)) * ‖v‖ ^ 2 ≤
        (F.metric t).pullbackCoefficients Φ x v v ∧
      (F.metric t).pullbackCoefficients Φ x v v ≤
        (b0 * Real.exp (54 * K * τ)) * ‖v‖ ^ 2 := by
  have h0 : (0 : ℝ) ∈ Icc (-τ) 0 := ⟨by linarith, le_rfl⟩
  let w := mfderiv (𝓡 3) (𝓡 3) Φ x v
  have hnonneg (s : ℝ) : 0 ≤ (F.metric s).inner (Φ x) w w := by
    by_cases hw : w = 0
    · simp [hw]
    · exact ((F.metric s).pos _ _ hw).le
  have hRic : ∀ s ∈ Icc (-τ) 0,
      |(F.connection s).ricci (Φ x) w w| ≤ (27 * K) * (F.metric s).inner (Φ x) w w := by
    intro s hs
    have h := (F.connection s).abs_ricci_quadratic_le_curvatureTensorNorm (Φ x) w
    have hdim : Module.finrank ℝ (TangentSpace (𝓡 3) (Φ x)) = 3 :=
      finrank_euclideanSpace_fin
    simp only [Fintype.card_fin, hdim] at h
    norm_num at h
    exact h.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hcurv s hs _
        ⟨x, Metric.closedBall_subset_ball hρR hx, rfl⟩) (by norm_num)) (hnonneg s))
  have htime := F.metric_inner_self_exp_bounds (convex_Icc (-τ) 0) (Subset.refl _)
    (Φ x) w (27 * K) hRic h0 ht
  have htau : |t - 0| ≤ τ := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  have hlo : Real.exp (-54 * K * τ) * (F.metric 0).pullbackCoefficients Φ x v v ≤
      (F.metric t).pullbackCoefficients Φ x v v := by
    apply le_trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (hnonneg 0)) htime.1
    nlinarith [mul_le_mul_of_nonneg_left htau (by positivity : 0 ≤ 54 * K)]
  have hhi : (F.metric t).pullbackCoefficients Φ x v v ≤
      Real.exp (54 * K * τ) * (F.metric 0).pullbackCoefficients Φ x v v := by
    apply htime.2.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (hnonneg 0))
    nlinarith [mul_le_mul_of_nonneg_left htau (by positivity : 0 ≤ 54 * K)]
  constructor
  · calc
      _ = Real.exp (-54 * K * τ) * (a0 * ‖v‖ ^ 2) := by ring
      _ ≤ Real.exp (-54 * K * τ) * (F.metric 0).pullbackCoefficients Φ x v v :=
        mul_le_mul_of_nonneg_left (hterminal x hx v).1 (Real.exp_pos _).le
      _ ≤ _ := hlo
  · apply hhi.trans
    calc
      _ ≤ Real.exp (54 * K * τ) * (b0 * ‖v‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (hterminal x hx v).2 (Real.exp_pos _).le
      _ = _ := by ring



theorem limitFinite_chart_curvature (P : RicciFlowCurvatureTheory.{u})
    {τ R K ρ a0 b0 : ℝ} (hτ : 0 < τ) (hK : 0 < K)
    (hρ : 0 < ρ) (hρR : 2 * ρ < R) (ha0 : 0 < a0) (j : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
      [IsManifold (𝓡 3) ∞ M] [T2Space M] [SecondCountableTopology M],
      ∀ (F : RicciFlow 3 M (Icc (-τ) 0))
        (Φ : PartialDiffeomorph (𝓡 3) (𝓡 3) E M ∞),
      Φ.source = Metric.ball 0 R →
      (∀ t ∈ Icc (-τ) 0, ∀ y ∈ Φ '' Metric.ball 0 R,
        (F.connection t).curvatureTensorNorm y ≤ K) →
      (∀ x ∈ Metric.closedBall 0 (2 * ρ), ∀ v : E,
        a0 * ‖v‖ ^ 2 ≤ (F.metric 0).pullbackCoefficients Φ x v v ∧
          (F.metric 0).pullbackCoefficients Φ x v v ≤ b0 * ‖v‖ ^ 2) →
      ∀ t ∈ Icc (-(τ / 2)) 0, ∀ x ∈ Metric.ball 0 (3 * ρ / 2),
        (F.connection t).curvatureDerivativeNorm j (Φ x) ≤ D := by
  let a := a0 * Real.exp (-54 * K * τ)
  let r := terminalSourceShiRadius a ρ
  have ha : 0 < a := mul_pos ha0 (Real.exp_pos _)
  have hr : 0 < r := terminalSourceShiRadius_pos ha hρ
  obtain ⟨D, hD, hShi⟩ := P.local_derivative_estimates 3 j K (K * τ) r
    hK (mul_pos hK hτ) hr
  refine ⟨D / (τ / 2) ^ ((j : ℝ) / 2), by positivity, ?_⟩
  intro M _ _ _ _ _ F Φ hsource hcurv hterminal t ht x hx
  have hcompact := terminalSourceCharts_compact_ball (F.metric (-τ)) Φ hsource
    hρ hρR ha
    (fun z hz v => (limitFinite_chart_closed_bounds hτ hK.le hρR F Φ hcurv hterminal
      ⟨le_rfl, by linarith⟩ hz v).1) hx
  have hmap : (fun s : ℝ => s + -τ) '' Icc 0 τ ⊆ Icc (-τ) 0 := by
    rintro _ ⟨s, hs, rfl⟩
    constructor <;> linarith [hs.1, hs.2]
  have hnontrivial : (Icc (0 : ℝ) τ).Nontrivial :=
    ⟨0, ⟨le_rfl, hτ.le⟩, τ, ⟨hτ.le, le_rfl⟩, hτ.ne⟩
  let G := F.translate (-τ) hmap ordConnected_Icc hnontrivial
  have htime : τ ≤ (K * τ) / K := by rw [mul_div_cancel_left₀ τ hK.ne']
  have hG0 : G.metric 0 = F.metric (-τ) := by
    change F.metric (0 + -τ) = F.metric (-τ)
    rw [zero_add]
  have hGc : IsCompact (closure ((G.metric 0).ball (Φ x) r)) := by
    rw [hG0]
    exact hcompact.1
  have hGcurv : ∀ s ∈ Icc 0 τ, ∀ y ∈ (G.metric 0).ball (Φ x) r,
      (G.connection s).curvatureTensorNorm y ≤ K := by
    intro s hs y hy
    rw [hG0] at hy
    exact hcurv (s + -τ) (hmap ⟨s, hs, rfl⟩) y (hcompact.2 hy)
  have hcentre : Φ x ∈ (G.metric 0).ball (Φ x) (r / 2) := by
    change (G.metric 0).edist (Φ x) (Φ x) < ENNReal.ofReal (r / 2)
    rw [M36.metric_edist_self]
    exact ENNReal.ofReal_pos.mpr (by positivity)
  have hs : t + τ ∈ Ioc 0 τ := by constructor <;> linarith [ht.1, ht.2]
  have hb := hShi M τ hτ htime G (Φ x) hGc hGcurv (t + τ) hs _ hcentre
  change (F.connection (t + τ + -τ)).curvatureDerivativeNorm j (Φ x) ≤ _ at hb
  rw [add_neg_cancel_right] at hb
  apply hb.trans (div_le_div_of_nonneg_left hD.le (by positivity) ?_)
  exact Real.rpow_le_rpow (by positivity) (by linarith [ht.1]) (by positivity)

end PoincareConjecture.M47
