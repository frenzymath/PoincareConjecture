import PoincareConjecture.Proofs.M47.TerminalCommonIntervalOriginalCoordinateCoherence
import PoincareConjecture.Proofs.M47.LimitCanonicalPhysicalCoefficientJets
import PoincareConjecture.Proofs.M47.BlowupControlsSequence
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.TransitionLimit

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ

private noncomputable local instance originalGermLimitDualAdd : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance originalGermLimitDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
private noncomputable local instance originalGermLimitBilinAdd : NormedAddCommGroup Bilin :=
  ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance originalGermLimitBilinSpace : NormedSpace ℝ Bilin :=
  ContinuousLinearMap.toNormedSpace

variable (F : ℕ → SurgeryFlowData.{u}) (W : ∀ k, M33RegularHistoryWindow (F k))
  (history : ∀ k, M33RegularHistoryData (W k)) (baseTime : ℕ → ℝ)
  (hbaseTime : ∀ k, baseTime k ∈ (history k).generalized.interval)
  (basePoint : ∀ k, ((history k).generalized.slice (baseTime k)).carrier)
  (hPositive : ∀ k, 0 < ((F k).connection (baseTime k)).scalarCurvature
    ((history k).history.forward (baseTime k) (hbaseTime k) (basePoint k)))
  (hDiverges : Tendsto (fun k => ((F k).connection (baseTime k)).scalarCurvature
    ((history k).history.forward (baseTime k) (hbaseTime k) (basePoint k))) atTop atTop)

local notation "V" => regularHistoryBlowupSequence F W history baseTime hbaseTime
  basePoint hPositive hDiverges

variable {J : Set ℝ} (G : GeneralizedBlowupConvergence
  (regularHistoryBlowupSequence F W history baseTime hbaseTime
    basePoint hPositive hDiverges) J)

private local instance originalGermTopology : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance originalGermCharts : ChartedSpace E G.limit.carrier.carrier :=
  G.limit.carrier.chartedSpace
private local instance originalGermManifold : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier :=
  G.limit.carrier.isManifold

theorem terminalCommonInterval_original_germ_metric
    (P : M47Predecessors.{u}) (rho : ℕ → ℕ) (hrho : StrictMono rho)
    (C : ℕ → GeneralizedSliceCarrier.{u}) (I : ℕ → Set ℝ)
    (U : ∀ n, Set (C n).carrier) (hIc : ∀ n, (I n).OrdConnected)
    (hU : ∀ n, IsOpen (U n))
    (e : ∀ n, GeneralizedFlowCylinder (history (G.subsequence (rho n))).generalized
      (C n) (baseTime (G.subsequence (rho n))) ((V).scale (G.subsequence (rho n)))
      (I n) (U n))
    (a : ∀ n, PartialDiffeomorph (𝓡 3) (𝓡 3) (C n).carrier E ∞)
    (t : ℝ) (ht : t ∈ J) (ht0 : t ≤ 0) (hI : ∀ n, Icc t 0 ⊆ I n)
    (q : G.limit.sliceCarrier.carrier) {D : Set E} (hD : IsOpen D)
    (A : E → Bilin) (T : E → E)
    (hA : ∀ x ∈ D, ∀ v w : E, Tendsto (fun n =>
      (V).scale (G.subsequence (rho n)) *
        ((history (G.subsequence (rho n))).generalized.metric
          (baseTime (G.subsequence (rho n)) +
            t / (V).scale (G.subsequence (rho n)))).pullbackCoefficients
          ((e n).forward t (hI n ⟨le_rfl, ht0⟩) ∘ (a n).symm) x v w)
      atTop (𝓝 (A x v w)))
    (hT : MapsTo T D (extChartAt (𝓡 3) q).target) :
    let Tn := fun n =>
      (((a n).symm.toOpenPartialHomeomorph.trans
        ((e n).spatialOpenPartialHomeomorph (hU n) 0 (hI n ⟨ht0, le_rfl⟩))).trans
          ((G.embedding (rho n)).spatialOpenPartialHomeomorph
            (G.exhaustion.space_open (rho n)) 0
            ⟨neg_nonpos.mpr (G.exhaustion.time_pos (rho n)).le, le_rfl⟩).symm).trans
              (limitCanonicalNativeChart q).toOpenPartialHomeomorph
    (∀ x ∈ D, ∀ᶠ n in atTop, x ∈ (Tn n).source) →
    (∀ m K, IsCompact K → K ⊆ D → TendstoUniformlyOn
      (fun n => iteratedFDeriv ℝ m (Tn n)) (iteratedFDeriv ℝ m T) atTop K) →
    ∀ x ∈ D, ∀ v w : E,
      (G.limit.flow.metric t).pullbackCoefficients (extChartAt (𝓡 3) q).symm (T x)
        (fderiv ℝ T x v) (fderiv ℝ T x w) = A x v w := by
  dsimp only
  intro hsource htransition
  let Tn := fun n =>
    (((a n).symm.toOpenPartialHomeomorph.trans
      ((e n).spatialOpenPartialHomeomorph (hU n) 0 (hI n ⟨ht0, le_rfl⟩))).trans
        ((G.embedding (rho n)).spatialOpenPartialHomeomorph
          (G.exhaustion.space_open (rho n)) 0
          ⟨neg_nonpos.mpr (G.exhaustion.time_pos (rho n)).le, le_rfl⟩).symm).trans
            (limitCanonicalNativeChart q).toOpenPartialHomeomorph
  let Aseq : ℕ → E → Bilin := fun n x =>
    (V).scale (G.subsequence (rho n)) •
      ((history (G.subsequence (rho n))).generalized.metric
        (baseTime (G.subsequence (rho n)) +
          t / (V).scale (G.subsequence (rho n)))).pullbackCoefficients
        ((e n).forward t (hI n ⟨le_rfl, ht0⟩) ∘ (a n).symm) x
  let Bseq : ℕ → E → Bilin := fun n =>
    M34.blowupCoordinateBilinear (G.embedding (rho n)) q t
  let B : E → Bilin :=
    (G.limit.flow.metric t).pullbackCoefficients (extChartAt (𝓡 3) q).symm
  have hBactual := limitCanonical_round_bilinear_coefficient_convergence P G q t ht
  have hB : TendstoLocallyUniformlyOn Bseq B atTop (extChartAt (𝓡 3) q).target := by
    apply CoordinateTransition.locallyUniformly_of_tendsto_zeroJet
      (isOpen_extChartAt_target q)
    intro K hK hKt entourage hentourage
    exact hrho.tendsto_atTop.eventually ((hBactual.jets 0 K hK hKt) entourage hentourage)
  have htime : ∀ᶠ n in atTop, t ∈ Icc (-G.exhaustion.time (rho n)) 0 := by
    filter_upwards [hrho.tendsto_atTop.eventually
      (G.exhaustion.time_cofinal {t} isCompact_singleton (singleton_subset_iff.mpr ht))]
      with n hn
    exact hn (mem_singleton t)
  apply CoordinateTransition.pullback_eq_of_tendsto
    (Aseq := Aseq) (Bseq := Bseq) (fseq := fun n => Tn n)
    (isOpen_extChartAt_target q) hA hB hBactual.smooth.continuousOn hT
    (fun x hx =>
      (CoordinateTransition.locallyUniformly_of_tendsto_zeroJet hD
        (htransition 0)).tendsto_at hx)
  · intro x hx v
    have hj := (htransition 1 {x} isCompact_singleton
      (singleton_subset_iff.mpr hx)).tendsto_at (mem_singleton x)
    have hev := ContinuousMultilinearMap.uniformContinuous_eval_const
      (𝕜 := ℝ) (F := E) (fun _ : Fin 1 => v)
    simpa only [Function.comp_def, iteratedFDeriv_one_apply] using
      (hev.continuous.tendsto _).comp hj
  · intro x hx
    filter_upwards [hsource x hx, htime] with n hn htn v w
    have hJ : Icc t 0 ⊆ Icc (-G.exhaustion.time (rho n)) 0 :=
      Icc_subset_Icc htn.1 le_rfl
    have hcoord := (terminalCommonInterval_original_coordinate_coherence
      (history (G.subsequence (rho n))) (e n) (G.embedding (rho n))
      (hIc n) ordConnected_Icc (hU n) (G.exhaustion.space_open (rho n))
      ht0 (hI n) hJ (a n) (limitCanonicalNativeChart q)).2.2 x hn v w
    have htarget : Tn n x ∈ (extChartAt (𝓡 3) q).target :=
      (limitCanonicalNativeChart q).map_source hn.2
    have hback : (extChartAt (𝓡 3) q).symm (Tn n x) =
        ((G.embedding (rho n)).spatialOpenPartialHomeomorph
          (G.exhaustion.space_open (rho n)) 0
          ⟨neg_nonpos.mpr (G.exhaustion.time_pos (rho n)).le, le_rfl⟩).symm
            ((e n).spatialOpenPartialHomeomorph (hU n) 0 (hI n ⟨ht0, le_rfl⟩)
              ((a n).symm x)) :=
      (limitCanonicalNativeChart q).toPartialEquiv.left_inv hn.2
    have hspace : (extChartAt (𝓡 3) q).symm (Tn n x) ∈
        G.exhaustion.space (rho n) := by
      rw [hback]
      exact ((G.embedding (rho n)).spatialOpenPartialHomeomorph
        (G.exhaustion.space_open (rho n)) 0
        ⟨neg_nonpos.mpr (G.exhaustion.time_pos (rho n)).le, le_rfl⟩).map_target hn.1.2
    have hread := limitCanonical_round_reconstructed_eq_chartForm
      (G.embedding (rho n)) (G.exhaustion.space_open (rho n)) q t htn
      (Tn n x) htarget hspace
    change M34.blowupCoordinateBilinear (G.embedding (rho n)) q t (Tn n x)
      (fderiv ℝ (Tn n) x v) (fderiv ℝ (Tn n) x w) = Aseq n x v w
    rw [M34.blowupCoordinateBilinear, hread]
    exact hcoord

end PoincareConjecture.M47
