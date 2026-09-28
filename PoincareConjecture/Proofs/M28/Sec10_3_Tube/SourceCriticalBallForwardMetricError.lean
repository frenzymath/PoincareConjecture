import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallRawChartBounds
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.LimitFiniteChartBounds
import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.NeckGeometry.ForwardCylinderErrors











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

open tube PoincareConjecture.Proofs.M28.NeckTransfer PoincareConjecture.Proofs.M28.FiniteHessian

variable {epsilon C A : ℝ}
  {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
    ((n : ℝ) + 1) ((n : ℝ) + 1)}

set_option maxHeartbeats 2400000 in




theorem exists_regularRawStage_forward_metric_error (H : CounterexampleNeckFamily E)
    (T : ∀ k, SourceTubeData (H.segment k)) (A1 : ℝ) (hA1 : 0 < A1)
    (phi : ℕ → ℕ)
    (G : RegularPointedMetricConvergence
      (fun k => H.tubeCriticalMetric T A1 (phi k))
      (fun k => H.tubeCriticalBase T A1 hA1 (phi k))) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ (N : EpsilonNeck G.limitMetric) (j : ℕ), N.carrier ⊆ G.exhaustion j →
      ∀ n : ℕ, n + 1 ≤ ⌊N.epsilon⁻¹⌋₊ → ∀ rho : ℝ, 0 < rho →
        ∃ K : ℕ, ∀ k ≥ K, ∀ z : RoundCylinderSpace,
          z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ → ∀ r ≤ n + 1,
            ‖iteratedFDeriv ℝ r (fun x =>
              (H.normalizedSliceMetric (phi (G.subsequence k))).pullbackCoefficients
                (H.regularRawStageDiffeomorph T A1 hA1 phi G k ∘
                  cylinderNeckChart N z.1 z.2) x -
              G.limitMetric.pullbackCoefficients (cylinderNeckChart N z.1 z.2) x) 0‖ ≤
                rho := by
  classical
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro N j hNstage n hn
  let idx := fun k => phi (G.subsequence k)
  let e := H.regularRawStageDiffeomorph T A1 hA1 phi G
  have hmono : Monotone G.exhaustion := monotone_nat_of_le_succ
    (fun k => subset_closure.trans (G.exhaustion_step k))
  obtain ⟨F, Cset, hF, hcover⟩ := G.exists_finite_stage_chart_cover j
  let S := {q : G.limitCarrier.carrier // q ∈ F}
  let q : S → G.limitCarrier.carrier := Subtype.val
  let Kset := fun l : S => (extChartAt (𝓡 3) (q l)) '' Cset (q l)
  have hK (l : S) : IsCompact (Kset l) := (hF l.1 l.2).2.2.2.2.1
  have htarget (l : S) : Kset l ⊆ (extChartAt (𝓡 3) (q l)).target :=
    (hF l.1 l.2).2.2.2.2.2
  have hstage (l : S) (y : EuclideanSpace ℝ (Fin 3)) (hy : y ∈ Kset l) :
      (extChartAt (𝓡 3) (q l)).symm y ∈ G.exhaustion (j + 1) := by
    obtain ⟨x, hx, rfl⟩ := hy
    have hc := (hF l.1 l.2).2.2.2.1 hx
    rw [(extChartAt (𝓡 3) (q l)).left_inv hc.1]
    exact hc.2
  obtain ⟨a, b, B, ha, _, _, hbounds⟩ :=
    G.exists_limit_finite_chart_bounds q Kset hK htarget (n + 1)
  let J := {v : ℕ × RoundCylinderSpace × S // j ≤ v.1 ∧
    v.2.1.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ ∧
    N.coordinate_map v.2.1 ∈ Cset (q v.2.2)}
  let y := fun i : J => (extChartAt (𝓡 3) (q i.1.2.2)) (N.coordinate_map i.1.2.1)
  have hy (i : J) : y i ∈ Kset i.1.2.2 := mem_image_of_mem _ i.2.2.2
  have hp (i : J) : N.coordinate_map i.1.2.1 ∈
      (extChartAt (𝓡 3) (q i.1.2.2)).source :=
    ((hF i.1.2.2.1 i.1.2.2.2).2.2.2.1 i.2.2.2).1
  have hcap (i : J) : N.carrier ⊆ (e i.1.1).source := by
    rw [H.regularRawStageDiffeomorph_source]
    exact hNstage.trans (hmono i.2.1)
  have hBj : HasUniformJetBoundsAt (n + 1)
      (fun i : J => G.limitMetric.pullbackCoefficients (extChartAt (𝓡 3) (q i.1.2.2)).symm)
      y := by
    intro r hr
    exact ⟨B, fun i => (hbounds i.1.2.2 (y i) (hy i)).2 r hr⟩
  have hmap := hasUniformJetBoundsAt_fixedCylinderCoordinates_fderiv N
    (fun i : J => i.1.2.1.1) (fun i => i.1.2.1.2) (fun i => q i.1.2.2)
    (fun i => i.2.2.1) hp n hn hBj ha
    (fun i v => (hbounds i.1.2.2 (y i) (hy i)).1 v |>.1)
  have herror : ∀ delta : ℝ, 0 < delta → ∃ K : ℕ, ∀ i : J, K ≤ i.1.1 →
      ∀ r ≤ n + 1, ‖iteratedFDeriv ℝ r
          ((H.normalizedSliceMetric (idx i.1.1)).pullbackCoefficients
            (e i.1.1 ∘ (extChartAt (𝓡 3) (q i.1.2.2)).symm)) (y i) -
        iteratedFDeriv ℝ r
          (G.limitMetric.pullbackCoefficients (extChartAt (𝓡 3) (q i.1.2.2)).symm) (y i)‖ ≤
            delta := by
    intro delta hdelta
    obtain ⟨K, htail⟩ := eventually_atTop.mp
      (H.eventually_regularRawStage_finite_chart_jet_error T A1 hA1 phi G
        q Kset (j + 1) hK htarget hstage (n + 1) delta hdelta)
    exact ⟨K, fun i hi r hr => htail i.1.1 hi i.1.2.2 (y i) (hy i) r hr⟩
  have htail := exists_forwardCylinder_metric_error_tail
    (fun i : J => H.normalizedSliceMetric (idx i.1.1)) (fun i => e i.1.1) N hcap
    (fun i => i.1.2.1.1) (fun i => i.1.2.1.2) (fun i => q i.1.2.2)
    (fun i => i.2.2.1) hp (n + 1) (fun i => i.1.1) hmap herror
  intro rho hrho
  obtain ⟨K, htailK⟩ := htail rho hrho
  refine ⟨max j K, ?_⟩
  intro k hk z hz r hr
  have hjk : j ≤ k := (le_max_left _ _).trans hk
  have hzstage := hNstage (N.coordinate_map_mem_of_axial z hz)
  obtain ⟨q₀, hq₀⟩ := mem_iUnion.mp (hcover (subset_closure hzstage))
  obtain ⟨hqF, hqC⟩ := mem_iUnion.mp hq₀
  let l : S := ⟨q₀, hqF⟩
  let i : J := ⟨(k, z, l), hjk, hz, interior_subset hqC⟩
  exact htailK i ((le_max_right _ _).trans hk) r hr

end PoincareConjecture.M28.CounterexampleNeckFamily
