import PoincareConjecture.Proofs.M35.CapGeometry.SelectedCoordinateJets
import PoincareConjecture.Proofs.M35.Thm12_28.MetricConnectionJets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.OrdinaryRealization

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 3)
local notation "B" => V →L[ℝ] V →L[ℝ] ℝ

local instance selectedCoordinateDualNormedGroup : NormedAddCommGroup (V →L[ℝ] ℝ) :=
  inferInstance
local instance selectedCoordinateDualNormedSpace : NormedSpace ℝ (V →L[ℝ] ℝ) := inferInstance
local instance selectedCoordinateMetricNormedGroup : NormedAddCommGroup B := inferInstance
local instance selectedCoordinateMetricNormedSpace : NormedSpace ℝ B := inferInstance

theorem blowupSequence_fixed_coordinate_metric_jets
    (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤)) :
    letI : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
    letI : ChartedSpace V L.limit.carrier.carrier := L.limit.carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
    ∀ (coordinate : V → L.limit.sliceCarrier.carrier)
      (_hc : ContMDiff (𝓡 3) (𝓡 3) ∞ coordinate)
      (pseq : ℕ → V) (p : V) (_hp : Tendsto pseq atTop (𝓝 p))
      (sigma : ℕ → ℕ) (_hsigma : Tendsto sigma atTop atTop)
      (gseq : ℕ → RiemannianMetric 3 V) (g : RiemannianMetric 3 V),
      let F (k : ℕ) (z : L.limit.sliceCarrier.carrier) :=
        ((L.embedding (sigma k)).forward 0
          ⟨neg_nonpos.mpr (L.exhaustion.time_pos (sigma k)).le, le_rfl⟩ z).val
      let Q (k : ℕ) := (blowupSequence P E t x ht hR).scale (L.subsequence (sigma k))
      (∀ᶠ k in atTop, (gseq k).euclideanCoefficients =ᶠ[𝓝 (pseq k)]
        fun y => Q k • (E.flow.metric (t (L.subsequence (sigma k)))).pullbackCoefficients
          (F k ∘ coordinate) y) →
      (g.euclideanCoefficients =ᶠ[𝓝 p]
        (L.limit.flow.metric 0).pullbackCoefficients coordinate) →
      ∀ r : ℕ, Tendsto (fun k => iteratedFDeriv ℝ r (gseq k).euclideanCoefficients (pseq k))
        atTop (𝓝 (iteratedFDeriv ℝ r g.euclideanCoefficients p)) := by
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : ChartedSpace V L.limit.carrier.carrier := L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  intro coordinate hcoord pseq p hp sigma hsigma gseq g
  dsimp only
  intro hcoeff hlimit r
  let F (k : ℕ) (z : L.limit.sliceCarrier.carrier) :=
    ((L.embedding (sigma k)).forward 0
      ⟨neg_nonpos.mpr (L.exhaustion.time_pos (sigma k)).le, le_rfl⟩ z).val
  let Q (k : ℕ) := (blowupSequence P E t x ht hR).scale (L.subsequence (sigma k))
  let a := coordinate p
  let c := extChartAt (𝓡 3) a
  let z := c a
  have ha : a ∈ c.source := mem_extChartAt_source a
  have hz : z ∈ c.target := mem_extChartAt_target a
  have hcz : c.symm z = a := c.left_inv ha
  have hcover : a ∈ ⋃ j, L.exhaustion.space j :=
    (congrArg (fun U : Set L.limit.sliceCarrier.carrier => a ∈ U)
      L.exhaustion.space_covers).mpr (mem_univ a)
  obtain ⟨j, haj⟩ := mem_iUnion.mp hcover
  let W := c.target ∩ c.symm ⁻¹' L.exhaustion.space j
  have hW : IsOpen W := (continuousOn_extChartAt_symm a).isOpen_inter_preimage
    (isOpen_extChartAt_target a) (L.exhaustion.space_open j)
  have hzW : z ∈ W := by
    refine ⟨hz, ?_⟩
    change c.symm z ∈ L.exhaustion.space j
    rwa [hcz]
  obtain ⟨δ, hδ, hδW⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hW.mem_nhds hzW)
  let K : Set (ℝ × V) := ({0} : Set ℝ) ×ˢ Metric.closedBall z δ
  have hK : IsCompact K := isCompact_singleton.prod (isCompact_closedBall z δ)
  have hKU : K ⊆ {b | b ∈ blowupMetricChartDomain L.limit a ∧
      c.symm b.2 ∈ L.exhaustion.space j} := by
    rintro ⟨s, y⟩ ⟨hs, hy⟩
    have hs0 : s = 0 := mem_singleton_iff.mp hs
    subst s
    refine ⟨⟨?_, (hδW hy).1⟩, (hδW hy).2⟩
    simp [blowupBackwardInterval]
  have hcp : ContDiffAt ℝ ∞ (c ∘ coordinate) p := by
    have hchart : a ∈ (chartAt V a).source := mem_chart_source V a
    exact ((contMDiffAt_extChartAt' (I := 𝓡 3) (n := ∞) hchart).comp p (hcoord p)).contDiffAt
  have hsource : ∀ᶠ k in atTop, coordinate (pseq k) ∈ c.source :=
    ((hcoord p).continuousAt.tendsto.comp hp).eventually
      ((isOpen_extChartAt_source (I := 𝓡 3) a).mem_nhds ha)
  have hpoints : ∀ᶠ k in atTop, c (coordinate (pseq k)) ∈ Metric.closedBall z δ :=
    (hcp.continuousAt.tendsto.comp hp).eventually (Metric.closedBall_mem_nhds z hδ)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hsource.and hpoints)
  let pseq' (k : ℕ) := if N ≤ k then pseq k else p
  have hpseq' : pseq' =ᶠ[atTop] pseq := by
    filter_upwards [eventually_ge_atTop N] with k hk
    exact if_pos hk
  have hp' : Tendsto pseq' atTop (𝓝 p) := hp.congr' hpseq'.symm
  have hcseq' (k : ℕ) : coordinate (pseq' k) ∈ c.source := by
    by_cases hk : N ≤ k
    · simpa only [pseq', if_pos hk] using (hN k hk).1
    · simpa only [pseq', if_neg hk] using ha
  have hpoints' (k : ℕ) : (0, c (coordinate (pseq' k))) ∈ K := by
    refine ⟨mem_singleton 0, ?_⟩
    by_cases hk : N ≤ k
    · simpa only [pseq', if_pos hk] using (hN k hk).2
    · simpa only [pseq', if_neg hk] using Metric.mem_closedBall_self hδ.le
  apply metric_jet_tendsto_of_scalar_jets pseq p
  intro i j'
  let v := EuclideanSpace.basisFun (Fin 3) ℝ i
  let w := EuclideanSpace.basisFun (Fin 3) ℝ j'
  let H (y : V) := (L.limit.flow.metric 0).pullbackCoefficients coordinate y v w
  let Bseq (k : ℕ) (y : V) :=
    Q k * (E.flow.metric (t (L.subsequence (sigma k)))).pullbackCoefficients
      (F k ∘ coordinate) y v w
  have hH (y : V) : ContDiffAt ℝ ∞ H y :=
    (((L.limit.flow.metric 0).contDiffAt_pullbackCoefficients (hcoord y)).clm_apply
      contDiffAt_const).clm_apply contDiffAt_const
  have herr : Tendsto (fun k => iteratedFDeriv ℝ r
      (fun y => Bseq k y - H y) (pseq k)) atTop (𝓝 0) := by
    have hh := blowupSequence_fixed_coordinate_error_jets P E t x ht hR L
      coordinate hcoord pseq' p hp' a ha hcseq' j K hK hKU sigma hsigma hpoints' r v w
    apply hh.congr'
    filter_upwards [hpseq'] with k hk
    exact congrArg (iteratedFDeriv ℝ r (fun y => Bseq k y - H y)) hk
  have hlim : (fun y => g.inner y v w) =ᶠ[𝓝 p] H :=
    hlimit.mono fun y hy => congrArg (fun b : B => b v w) hy
  rw [(hlim.iteratedFDeriv ℝ r).self_of_nhds]
  have hr : (r : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top (a := (r : ℕ∞))
  have hmodel := ((hH p).continuousAt_iteratedFDeriv hr).tendsto.comp hp
  have hsum := herr.add hmodel
  simp only [zero_add] at hsum
  apply hsum.congr'
  filter_upwards [hcoeff] with k hk
  have hBk : (fun y => (gseq k).inner y v w - H y) =ᶠ[𝓝 (pseq k)]
      (fun y => Bseq k y - H y) := by
    filter_upwards [hk] with y hy
    have hval := congrArg (fun b : B => b v w) hy
    exact congrArg (fun z : ℝ => z - H y) hval
  have hgs : ContDiffAt ℝ ∞ (fun y => (gseq k).inner y v w) (pseq k) :=
    (((gseq k).contDiffAt_euclideanCoefficients (pseq k)).clm_apply
      contDiffAt_const).clm_apply contDiffAt_const
  have hd := (hBk.iteratedFDeriv ℝ r).self_of_nhds
  rw [fun_iteratedFDeriv_sub_apply (hgs.of_le hr) ((hH (pseq k)).of_le hr)] at hd
  exact (congrArg (fun A => A + iteratedFDeriv ℝ r H (pseq k)) hd.symm).trans
    (sub_add_cancel _ _)

end

end PoincareConjecture.M35.OrdinaryRealization
