import PoincareConjecture.Proofs.M47.LimitFiniteChartJets
import PoincareConjecture.Proofs.M47.TerminalSourceJetsMixed

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "V" => E →L[ℝ] E →L[ℝ] ℝ

private noncomputable local instance finiteChartMixedDualAdd : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance finiteChartMixedDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
private noncomputable local instance finiteChartMixedBilinAdd :
    NormedAddCommGroup V := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance finiteChartMixedBilinSpace :
    NormedSpace ℝ V := ContinuousLinearMap.toNormedSpace

variable {α : Type v} (l : Filter α) (M : α → Type u)
  [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace E (M k)]
  [∀ k, IsManifold (𝓡 3) ∞ (M k)] [∀ k, T2Space (M k)]
  [∀ k, SecondCountableTopology (M k)]

theorem limitFinite_chart_mixed_jets (P : RicciFlowCurvatureTheory.{u})
    {τ R K ρ a0 b0 : ℝ} (hτ : 0 < τ) (hK : 0 < K)
    (hρ : 0 < ρ) (hρR : 2 * ρ < R) (ha0 : 0 < a0) (hb0 : 0 ≤ b0)
    (F : ∀ k, RicciFlow 3 (M k) (Icc (-τ) 0))
    (Φ : ∀ k, PartialDiffeomorph (𝓡 3) (𝓡 3) E (M k) ∞)
    (hsource : ∀ k, (Φ k).source = Metric.ball 0 R)
    (hraw : ∀ᶠ k in l, ∀ t ∈ Icc (-τ) 0, ∀ y ∈ Φ k '' Metric.ball 0 R,
      ((F k).connection t).curvatureTensorNorm y ≤ K)
    (hquad : ∀ᶠ k in l, ∀ x ∈ Metric.closedBall 0 (2 * ρ), ∀ v : E,
      a0 * ‖v‖ ^ 2 ≤ ((F k).metric 0).pullbackCoefficients (Φ k) x v v ∧
        ((F k).metric 0).pullbackCoefficients (Φ k) x v v ≤ b0 * ‖v‖ ^ 2)
    (hterminal : ∀ m : ℕ, ∃ Z : ℝ, 1 ≤ Z ∧ ∀ᶠ k in l,
      ∀ x ∈ Metric.closedBall 0 ρ, ∀ j ≤ m,
        ‖iteratedFDeriv ℝ j (((F k).metric 0).pullbackCoefficients (Φ k)) x‖ ≤ Z) :
    ∀ m : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k in l,
      ∀ t ∈ Ioo (-(τ / 2)) 0, ∀ x ∈ Metric.closedBall 0 ρ,
        ‖iteratedFDeriv ℝ m (fun p : ℝ × E =>
          ((F k).metric p.1).pullbackCoefficients (Φ k) p.2) (t, x)‖ ≤ B := by
  let f := fun k (p : ℝ × E) => ((F k).metric p.1).pullbackCoefficients (Φ k) p.2
  let J := fun _ : α => Ioo (-τ) 0
  let U := fun _ : α => Metric.ball (0 : E) R
  let S := fun _ : α => Ioo (-(τ / 2)) 0 ×ˢ Metric.closedBall (0 : E) ρ
  have hsubset : ∀ k, S k ⊆ J k ×ˢ U k := by
    intro k p hp
    exact ⟨⟨by linarith [hp.1.1], hp.1.2⟩,
      Metric.closedBall_subset_ball (by linarith : ρ < R) hp.2⟩
  have hPhi (k : α) : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (Φ k) (U k) := by
    simpa only [hsource k] using (Φ k).contMDiffOn
  have hPhiInv (k : α) (x : E) (hx : x ∈ U k) :
      (mfderiv (𝓡 3) (𝓡 3) (Φ k) x).IsInvertible :=
    ⟨((Φ k).isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
      ((hsource k).symm ▸ hx)).mfderivToContinuousLinearEquiv (by simp), rfl⟩
  have hsmooth : ∀ k, ContDiffOn ℝ ∞ (f k) (J k ×ˢ U k) := by
    intro k
    exact (M44.contDiffOn_pullbackCoefficients_within (F k) Metric.isOpen_ball
      (hPhi k)).mono (prod_mono Ioo_subset_Icc_self (Subset.refl _))
  have hinv : ∀ k p, p ∈ J k ×ˢ U k → (f k p).IsInvertible := by
    intro k p hp
    exact ((F k).metric p.1).isInvertible_pullbackCoefficients (hPhiInv k p.2 hp.2).injective
  have hevol : ∀ k t, t ∈ J k → ∀ x ∈ U k,
      HasDerivAt (fun s => f k (s, x))
        (SpacetimeBounds.ricciFlowOperator 3
          (SpacetimeBounds.metricTwoJet (fun y => f k (t, y)) x)) t := by
    intro k t ht x hx
    exact M44.hasDerivAt_pullbackCoefficients_ricci
      (M44.closedSlabInterior (by linarith : -τ < 0) (F k)) isOpen_Ioo
      Metric.isOpen_ball (hPhi k) (hPhiInv k) ht hx
  have helliptic : ∀ᶠ k in l, ∀ p ∈ S k, ∀ v,
      (a0 * Real.exp (-54 * K * τ)) * ‖v‖ ^ 2 ≤ f k p v v := by
    filter_upwards [hraw, hquad] with k hk hq p hp v
    exact (limitFinite_chart_closed_bounds hτ hK.le hρR (F k) (Φ k) hk hq
      ⟨by linarith [hp.1.1], hp.1.2.le⟩
      (Metric.closedBall_subset_closedBall (by linarith) hp.2) v).1
  have hspatial : ∀ m : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k in l,
      ∀ p ∈ S k, ∀ j ≤ m, ‖iteratedFDeriv ℝ j (fun x => f k (p.1, x)) p.2‖ ≤ B := by
    intro m
    obtain ⟨Z, hZ, hz⟩ := hterminal m
    obtain ⟨B, hB, hbound⟩ := limitFinite_chart_spatial_jets P hτ hK hρ hρR ha0 hb0 hZ m
    refine ⟨B, hB, ?_⟩
    filter_upwards [hraw, hquad, hz] with k hk hq hj p hp n hn
    exact hbound (F k) (Φ k) (hsource k) hk hq hj
      p.1 (Ioo_subset_Icc_self hp.1) p.2 hp.2 n hn
  have h := M44.eventually_coordinate_spacetime_jet_bound l 3 f J U S hsmooth
    (fun _ => isOpen_Ioo) (fun _ => Metric.isOpen_ball) hsubset hinv hevol
    (mul_pos ha0 (Real.exp_pos _)) helliptic hspatial
  intro m
  obtain ⟨B, hB, hbound⟩ := h m
  exact ⟨B, hB, hbound.mono fun k hk t ht x hx => hk (t, x) ⟨ht, hx⟩⟩

theorem limitFinite_chart_mixed_readout (P : RicciFlowCurvatureTheory.{u})
    {τ R K ρ a0 b0 : ℝ} (hτ : 0 < τ) (hK : 0 < K)
    (hρ : 0 < ρ) (hρR : 2 * ρ < R) (ha0 : 0 < a0) (hb0 : 0 ≤ b0)
    (F : ∀ k, RicciFlow 3 (M k) (Icc (-τ) 0))
    (Φ : ∀ k, PartialDiffeomorph (𝓡 3) (𝓡 3) E (M k) ∞)
    (hsource : ∀ k, (Φ k).source = Metric.ball 0 R)
    (hraw : ∀ᶠ k in l, ∀ t ∈ Icc (-τ) 0, ∀ y ∈ Φ k '' Metric.ball 0 R,
      ((F k).connection t).curvatureTensorNorm y ≤ K)
    (hquad : ∀ᶠ k in l, ∀ x ∈ Metric.closedBall 0 (2 * ρ), ∀ v : E,
      a0 * ‖v‖ ^ 2 ≤ ((F k).metric 0).pullbackCoefficients (Φ k) x v v ∧
        ((F k).metric 0).pullbackCoefficients (Φ k) x v v ≤ b0 * ‖v‖ ^ 2)
    (hterminal : ∀ m : ℕ, ∃ Z : ℝ, 1 ≤ Z ∧ ∀ᶠ k in l,
      ∀ x ∈ Metric.closedBall 0 ρ, ∀ j ≤ m,
        ‖iteratedFDeriv ℝ j (((F k).metric 0).pullbackCoefficients (Φ k)) x‖ ≤ Z)
    (f : α → ℝ × E → V)
    (hactual : ∀ᶠ k in l, EqOn (f k)
      (fun p : ℝ × E => ((F k).metric p.1).pullbackCoefficients (Φ k) p.2)
      (Ioo (-τ) 0 ×ˢ Metric.ball 0 R)) (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k in l,
      ∀ t ∈ Ioo (-(τ / 2)) 0, ∀ x ∈ Metric.closedBall 0 ρ,
        ‖iteratedFDeriv ℝ m (f k) (t, x)‖ ≤ B := by
  obtain ⟨B, hB, hbound⟩ := limitFinite_chart_mixed_jets l M P hτ hK hρ hρR ha0 hb0
    F Φ hsource hraw hquad hterminal m
  refine ⟨B, hB, ?_⟩
  filter_upwards [hbound, hactual] with k hk heq t ht x hx
  have hmem : (t, x) ∈ Ioo (-τ) 0 ×ˢ Metric.ball (0 : E) R :=
    ⟨⟨by linarith [ht.1], ht.2⟩, Metric.closedBall_subset_ball (by linarith) hx⟩
  have hgerm : f k =ᶠ[𝓝 (t, x)]
      (fun p : ℝ × E => ((F k).metric p.1).pullbackCoefficients (Φ k) p.2) := by
    filter_upwards [(isOpen_Ioo.prod Metric.isOpen_ball).mem_nhds hmem] with p hp
    exact heq hp
  rw [(hgerm.iteratedFDeriv (𝕜 := ℝ) m).eq_of_nhds]
  exact hk t ht x hx

end PoincareConjecture.M47
