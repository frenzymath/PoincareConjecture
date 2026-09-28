import PoincareConjecture.Proofs.M47.TerminalSourceJetsSpatial
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_CompactnessFeedJets
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_RicciTimeGluing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "V" => E →L[ℝ] E →L[ℝ] ℝ

variable {α : Type v} (l : Filter α) (M : α → Type u)
  [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace E (M k)]
  [∀ k, IsManifold (𝓡 3) ∞ (M k)] [∀ k, T2Space (M k)]
  [∀ k, SecondCountableTopology (M k)]

theorem terminalSourceJets_mixed (P : RicciFlowCurvatureTheory.{u})
    {τ R H ρ : ℝ} (hτ : 0 < τ) (hH : 0 < H) (hρ : 0 < ρ) (hρR : 2 * ρ < R)
    (hsmall : ∀ s : ℝ, |s| ≤ 2 * ρ →
      (H * s ^ 2) * Real.exp (max 1 (H * s ^ 2)) ≤ 3)
    (F : ∀ k, RicciFlow 3 (M k) (Icc (-τ) 0))
    (C : ∀ k, TerminalSourceChart ((F k).metric 0) R)
    (hraw : ∀ᶠ k in l, ∀ t ∈ Icc (-τ) 0, ∀ y ∈ (C k).chart '' Metric.ball 0 R,
      ((F k).connection t).curvatureTensorNorm y ≤ H) :
    ∀ m : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k in l,
      ∀ t ∈ Ioo (-(τ / 2)) 0, ∀ x ∈ Metric.closedBall 0 ρ,
        ‖iteratedFDeriv ℝ m (fun p : ℝ × E =>
          ((F k).metric p.1).pullbackCoefficients (C k).chart p.2) (t, x)‖ ≤ B := by
  let f := fun k (p : ℝ × E) => ((F k).metric p.1).pullbackCoefficients (C k).chart p.2
  let J := fun _ : α => Ioo (-τ) 0
  let U := fun _ : α => Metric.ball (0 : E) R
  let S := fun _ : α => Ioo (-(τ / 2)) 0 ×ˢ Metric.closedBall (0 : E) ρ
  have hsubset : ∀ k, S k ⊆ J k ×ˢ U k := by
    intro k p hp
    exact ⟨⟨by linarith [hp.1.1], hp.1.2⟩,
      Metric.closedBall_subset_ball (by linarith : ρ < R) hp.2⟩
  have hsmooth : ∀ k, ContDiffOn ℝ ∞ (f k) (J k ×ˢ U k) := by
    intro k
    exact (M44.contDiffOn_pullbackCoefficients_within (F k) Metric.isOpen_ball
      (C k).smooth).mono (prod_mono Ioo_subset_Icc_self (Subset.refl _))
  have hinv : ∀ k p, p ∈ J k ×ˢ U k → (f k p).IsInvertible := by
    intro k p hp
    exact ((F k).metric p.1).isInvertible_pullbackCoefficients ((C k).invertible hp.2).injective
  have hevol : ∀ k t, t ∈ J k → ∀ x ∈ U k,
      HasDerivAt (fun s => f k (s, x))
        (SpacetimeBounds.ricciFlowOperator 3
          (SpacetimeBounds.metricTwoJet (fun y => f k (t, y)) x)) t := by
    intro k t ht x hx
    exact M44.hasDerivAt_pullbackCoefficients_ricci
      (M44.closedSlabInterior (by linarith : -τ < 0) (F k)) isOpen_Ioo
      Metric.isOpen_ball (C k).smooth (fun y hy => (C k).invertible hy) ht hx
  have helliptic : ∀ᶠ k in l, ∀ p ∈ S k, ∀ v,
      terminalSourceLower H τ * ‖v‖ ^ 2 ≤ f k p v v := by
    filter_upwards [hraw] with k hk p hp v
    exact ((C k).closed_bounds hτ hH.le (F k) hρR hsmall hk
      ⟨by linarith [hp.1.1], hp.1.2.le⟩
      (Metric.closedBall_subset_closedBall (by linarith) hp.2) v).1
  have hspatial : ∀ m : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k in l,
      ∀ p ∈ S k, ∀ j ≤ m, ‖iteratedFDeriv ℝ j (fun x => f k (p.1, x)) p.2‖ ≤ B := by
    intro m
    obtain ⟨B, hB, hbound⟩ := terminalSourceJets_spatial P hτ hH hρ hρR hsmall m
    refine ⟨B, hB, hraw.mono ?_⟩
    intro k hk p hp j hj
    exact hbound (F k) (C k) hk p.1 (Ioo_subset_Icc_self hp.1) p.2 hp.2 j hj
  have h := M44.eventually_coordinate_spacetime_jet_bound l 3 f J U S hsmooth
    (fun _ => isOpen_Ioo) (fun _ => Metric.isOpen_ball) hsubset hinv hevol
    (terminalSourceLower_pos H τ) helliptic hspatial
  intro m
  obtain ⟨B, hB, hbound⟩ := h m
  exact ⟨B, hB, hbound.mono fun k hk t ht x hx => hk (t, x) ⟨ht, hx⟩⟩

theorem terminalSourceJets_eventually_mixed_on_buffer (P : RicciFlowCurvatureTheory.{u})
    {τ R H ρ : ℝ} (hτ : 0 < τ) (hH : 0 < H) (hρ : 0 < ρ) (hρR : 2 * ρ < R)
    (hsmall : ∀ s : ℝ, |s| ≤ 2 * ρ →
      (H * s ^ 2) * Real.exp (max 1 (H * s ^ 2)) ≤ 3)
    (F : ∀ k, RicciFlow 3 (M k) (Icc (-τ) 0))
    (C : ∀ k, TerminalSourceChart ((F k).metric 0) R)
    (hraw : ∀ᶠ k in l, ∀ t ∈ Icc (-τ) 0, ∀ y ∈ (C k).chart '' Metric.ball 0 R,
      ((F k).connection t).curvatureTensorNorm y ≤ H)
    (fminus : α → ℝ × E → V)
    (hactual : ∀ᶠ k in l, EqOn (fminus k)
      (fun p : ℝ × E => ((F k).metric p.1).pullbackCoefficients (C k).chart p.2)
      (Ioo (-τ) 0 ×ˢ Metric.ball 0 R))
    {K : Set E} (hK : K ⊆ Metric.closedBall 0 ρ) (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k in l, ∀ t ∈ Ioo (-(τ / 2)) 0, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ m (fminus k) (t, x)‖ ≤ B := by
  obtain ⟨B, hB, hbound⟩ := terminalSourceJets_mixed l M P hτ hH hρ hρR hsmall F C hraw m
  refine ⟨B, hB, ?_⟩
  filter_upwards [hbound, hactual] with k hk heq t ht x hx
  have hmem : (t, x) ∈ Ioo (-τ) 0 ×ˢ Metric.ball (0 : E) R :=
    ⟨⟨by linarith [ht.1], ht.2⟩, Metric.closedBall_subset_ball (by linarith) (hK hx)⟩
  have hgerm : fminus k =ᶠ[𝓝 (t, x)]
      (fun p : ℝ × E => ((F k).metric p.1).pullbackCoefficients (C k).chart p.2) := by
    filter_upwards [(isOpen_Ioo.prod Metric.isOpen_ball).mem_nhds hmem] with p hp
    exact heq hp
  rw [(hgerm.iteratedFDeriv (𝕜 := ℝ) m).eq_of_nhds]
  exact hk t ht x (hK hx)

end PoincareConjecture.M47
