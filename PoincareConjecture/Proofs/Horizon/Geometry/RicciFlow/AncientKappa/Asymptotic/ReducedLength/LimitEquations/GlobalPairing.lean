import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.LimitEquations.ChartDomain
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ConjugateHeat.Coordinates.GlobalPairing
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ConjugateHeat.PairingIntegrability


noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 600000

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology NNReal

universe u
namespace PoincareConjecture.AncientCompactTimeConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.secondCountable

open RicciFlow.ConjugateHeat

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution n M} {S : AncientRescalingSequence K}

theorem reducedLengthPullback_limit_continuousOn
    (G : AncientCompactTimeConvergence S) (P : AncientAsymptoticSolitonPredecessors K)
    {σ : ℕ → ℕ} (hσ : StrictMono σ) (l : G.limit.carrier.carrier × ℝ → ℝ)
    (hlim : TendstoLocallyUniformlyOn
      (fun k z => G.reducedLengthPullback (σ k) z.1 z.2) l atTop
        (univ ×ˢ Ioi (0 : ℝ))) :
    ContinuousOn l (univ ×ˢ Ioi (0 : ℝ)) := by
  intro z hz
  let e := chartAt (EuclideanSpace ℝ (Fin n)) z.1
  have hsource : z.1 ∈ e.source := mem_chart_source _ _
  have hcoord := (G.reducedLengthPullback_limit_coordinates_locallyLipschitz
    P hσ l hlim z.1).continuousOn
  have hzcoord : (e z.1, z.2) ∈ e.target ×ˢ Ioi (0 : ℝ) :=
    ⟨e.map_source hsource, hz.2⟩
  have hmap : ContinuousAt
      (fun y : G.limit.carrier.carrier × ℝ => (e y.1, y.2)) z :=
    ((e.continuousOn.continuousAt (e.open_source.mem_nhds hsource)).comp
      continuous_fst.continuousAt).prodMk continuous_snd.continuousAt
  have hc : ContinuousAt
      (fun y : G.limit.carrier.carrier × ℝ => l (e.symm (e y.1), y.2)) z :=
    ((hcoord _ hzcoord).continuousAt
      ((e.open_target.prod isOpen_Ioi).mem_nhds hzcoord)).comp'
        (f := fun y : G.limit.carrier.carrier × ℝ => (e y.1, y.2)) hmap
  apply ContinuousAt.continuousWithinAt
  apply hc.congr_of_eventuallyEq
  filter_upwards [(continuous_fst.tendsto z) (e.open_source.mem_nhds hsource)] with y hy
  exact (congrArg (fun x => l (x, y.2)) (e.left_inv hy)).symm

theorem reducedLengthPullback_limitDensity_continuousOn
    (G : AncientCompactTimeConvergence S) (P : AncientAsymptoticSolitonPredecessors K)
    {σ : ℕ → ℕ} (hσ : StrictMono σ) (l : G.limit.carrier.carrier × ℝ → ℝ)
    (hlim : TendstoLocallyUniformlyOn
      (fun k z => G.reducedLengthPullback (σ k) z.1 z.2) l atTop
        (univ ×ˢ Ioi (0 : ℝ))) :
    ContinuousOn (fun z : G.limit.carrier.carrier × ℝ =>
      z.2 ^ (-(n : ℝ) / 2) * Real.exp (-l z)) (univ ×ˢ Ioi (0 : ℝ)) := by
  have hl := G.reducedLengthPullback_limit_continuousOn P hσ l hlim
  exact (continuousOn_snd.rpow_const (fun z hz => Or.inl (ne_of_gt hz.2))).mul hl.neg.rexp

theorem limitReducedLength_weakPairing_nonneg_of_chart_support
    (G : AncientCompactTimeConvergence S) (P : AncientAsymptoticSolitonPredecessors K)
    {σ : ℕ → ℕ} (hσ : StrictMono σ) (l : G.limit.carrier.carrier × ℝ → ℝ)
    (hlim : TendstoLocallyUniformlyOn
      (fun k z => G.reducedLengthPullback (σ k) z.1 z.2) l atTop
        (univ ×ˢ Ioi (0 : ℝ)))
    (q : G.limit.carrier.carrier) {φ : G.limit.carrier.carrier × ℝ → ℝ}
    (hφ : ContMDiff ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ φ)
    (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) q).source ×ˢ Ioi (0 : ℝ))
    (hφ0 : ∀ z, 0 ≤ φ z) :
    0 ≤ weakPairing G.limit.flow
      (fun z : G.limit.carrier.carrier × ℝ =>
        z.2 ^ (-(n : ℝ) / 2) * Real.exp (-l z)) φ := by
  let e := (chartAt (EuclideanSpace ℝ (Fin n)) q).symm
  have hs : tsupport φ ⊆ e.target ×ˢ univ :=
    hφs.trans (Set.prod_mono Subset.rfl (subset_univ _))
  obtain ⟨hi, hw⟩ := G.limitReducedLength_heat_pairing_nonpos_on_chart
    P hσ l hlim q (contDiff_spacetimeChartPullback e contMDiffOn_chart_symm hφ hφc hs)
      (hasCompactSupport_spacetimeChartPullback e hφc hs)
      (tsupport_spacetimeChartPullback_subset e hφc hφs)
      (spacetimeChartPullback_nonneg e hφ0)
  rw [weakPairing_eq_neg_coordinate_pairing G.limit.flow e
    contMDiffOn_chart_symm contMDiffOn_chart
    (G.reducedLengthPullback_limitDensity_continuousOn P hσ l hlim) hφ hφc hφs hi]
  exact neg_nonneg.mpr hw



theorem limitReducedLength_weakPairing_nonneg
    (G : AncientCompactTimeConvergence S) (P : AncientAsymptoticSolitonPredecessors K)
    {σ : ℕ → ℕ} (hσ : StrictMono σ) (l : G.limit.carrier.carrier × ℝ → ℝ)
    (hlim : TendstoLocallyUniformlyOn
      (fun k z => G.reducedLengthPullback (σ k) z.1 z.2) l atTop
        (univ ×ˢ Ioi (0 : ℝ)))
    {α β : ℝ} (hα : 0 < α) {φ : G.limit.carrier.carrier × ℝ → ℝ}
    (hφ : ContMDiff ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ φ)
    (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ univ ×ˢ Ioo α β)
    (hφ0 : ∀ z, 0 ≤ φ z) :
    0 ≤ weakPairing G.limit.flow
      (fun z : G.limit.carrier.carrier × ℝ =>
        z.2 ^ (-(n : ℝ) / 2) * Real.exp (-l z)) φ := by
  let : LocallyCompactSpace G.limit.carrier.carrier :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) G.limit.carrier.carrier
  let : SigmaCompactSpace G.limit.carrier.carrier := by infer_instance
  let u := fun z : G.limit.carrier.carrier × ℝ =>
    z.2 ^ (-(n : ℝ) / 2) * Real.exp (-l z)
  have hu := G.reducedLengthPullback_limitDensity_continuousOn P hσ l hlim
  have huI : ContinuousOn u (univ ×ˢ Icc α β) :=
    hu.mono (fun z hz => ⟨mem_univ _, hα.trans_le hz.2.1⟩)
  have ht : ∀ τ ∈ Icc α β, -τ ∈ interior (Iio (0 : ℝ)) := by
    intro τ hτ
    rw [interior_Iio]
    exact neg_neg_of_pos (hα.trans_le hτ.1)
  let T := weakPairingLinearOfContinuousOn G.limit.flow ht huI
  let Φ : testFunctions (n := n)
      ((univ : Set G.limit.carrier.carrier) ×ˢ Ioo α β) := ⟨φ, hφ, hφc, hφs⟩
  obtain ⟨s, f, hfs, hfc, hfsub, hfchart, hf0, hsum⟩ :=
    exists_finite_spacetime_chart_decomposition hφ hφc
  let ψ := fun i : G.limit.carrier.carrier =>
    (⟨f i, hfs i, hfc i, (hfsub i).trans hφs⟩ : testFunctions (n := n)
      ((univ : Set G.limit.carrier.carrier) ×ˢ Ioo α β))
  have heq : ∑ i ∈ s, ψ i = Φ := by
    apply Subtype.ext
    funext z
    simpa only [Submodule.coe_sum, Finset.sum_apply] using hsum z
  have hpos (i : G.limit.carrier.carrier) : 0 ≤ T (ψ i) := by
    change 0 ≤ weakPairing G.limit.flow u (f i)
    apply G.limitReducedLength_weakPairing_nonneg_of_chart_support
      P hσ l hlim i (hfs i) (hfc i) ?_ (fun z => hf0 i z (hφ0 z))
    intro z hz
    exact ⟨(hfchart i hz).1, hα.trans (hφs (hfsub i hz)).2.1⟩
  change 0 ≤ T Φ
  rw [← heq, map_sum]
  exact Finset.sum_nonneg (fun i _ => hpos i)

end PoincareConjecture.AncientCompactTimeConvergence
