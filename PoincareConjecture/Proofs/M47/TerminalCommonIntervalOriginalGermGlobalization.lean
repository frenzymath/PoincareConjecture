import PoincareConjecture.Proofs.M47.TerminalCommonIntervalOriginalGermLimit
import PoincareConjecture.Proofs.M47.TerminalCommonIntervalChartGlobalization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

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

private local instance originalGlobalTopology : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance originalGlobalCharts : ChartedSpace E G.limit.carrier.carrier :=
  G.limit.carrier.chartedSpace
private local instance originalGlobalManifold : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier :=
  G.limit.carrier.isManifold

theorem terminalCommonInterval_original_germ_identification
    (P : M47Predecessors.{u}) (rho : ℕ → ℕ) (hrho : StrictMono rho)
    {M : Type v} [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) (d : M → G.limit.sliceCarrier.carrier)
    (aOriginal : ℕ → PartialDiffeomorph (𝓡 3) (𝓡 3) M E ∞)
    (q : ℕ → G.limit.sliceCarrier.carrier)
    (D : ℕ → Set E) (hD : ∀ i, IsOpen (D i))
    (hDb : ∀ i, MapsTo (fun x => d ((aOriginal i).symm x)) (D i)
      (extChartAt (𝓡 3) (q i)).source)
    (hcover : ∀ x : M, ∃ i, x ∈ (aOriginal i).source ∧ aOriginal i x ∈ D i)
    (hsmooth : ∀ i, ContDiffOn ℝ ∞
      (fun x => (extChartAt (𝓡 3) (q i)) (d ((aOriginal i).symm x))) (D i))
    (C : ℕ → ℕ → GeneralizedSliceCarrier.{u}) (I : ℕ → ℕ → Set ℝ)
    (U : ∀ i n, Set (C i n).carrier) (hIc : ∀ i n, (I i n).OrdConnected)
    (hU : ∀ i n, IsOpen (U i n))
    (e : ∀ i n, GeneralizedFlowCylinder (history (G.subsequence (rho n))).generalized
      (C i n) (baseTime (G.subsequence (rho n))) ((V).scale (G.subsequence (rho n)))
      (I i n) (U i n))
    (aRaw : ∀ i n, PartialDiffeomorph (𝓡 3) (𝓡 3) (C i n).carrier E ∞)
    (t : ℝ) (ht : t ∈ J) (ht0 : t ≤ 0) (hI : ∀ i n, Icc t 0 ⊆ I i n)
    (hA : ∀ i x, x ∈ D i → ∀ v w : E, Tendsto (fun n =>
      (V).scale (G.subsequence (rho n)) *
        ((history (G.subsequence (rho n))).generalized.metric
          (baseTime (G.subsequence (rho n)) +
            t / (V).scale (G.subsequence (rho n)))).pullbackCoefficients
          ((e i n).forward t (hI i n ⟨le_rfl, ht0⟩) ∘ (aRaw i n).symm) x v w)
      atTop (𝓝 (g.pullbackCoefficients (aOriginal i).symm x v w))) :
    let Tn := fun i n =>
      (((aRaw i n).symm.toOpenPartialHomeomorph.trans
        ((e i n).spatialOpenPartialHomeomorph (hU i n) 0
          (hI i n ⟨ht0, le_rfl⟩))).trans
            ((G.embedding (rho n)).spatialOpenPartialHomeomorph
              (G.exhaustion.space_open (rho n)) 0
              ⟨neg_nonpos.mpr (G.exhaustion.time_pos (rho n)).le, le_rfl⟩).symm).trans
                (limitCanonicalNativeChart (q i)).toOpenPartialHomeomorph
    (∀ i x, x ∈ D i → ∀ᶠ n in atTop, x ∈ (Tn i n).source) →
    (∀ i m K, IsCompact K → K ⊆ D i → TendstoUniformlyOn
      (fun n => iteratedFDeriv ℝ m (Tn i n))
      (iteratedFDeriv ℝ m
        (fun x => (extChartAt (𝓡 3) (q i)) (d ((aOriginal i).symm x)))) atTop K) →
    ∀ x : M, ∀ v w : TangentSpace (𝓡 3) x,
      g.inner x v w = (G.limit.flow.metric t).inner (d x)
        (mfderiv (𝓡 3) (𝓡 3) d x v) (mfderiv (𝓡 3) (𝓡 3) d x w) := by
  dsimp only
  intro hsource hjets
  apply terminalCommonInterval_metric_of_coordinate_rows d aOriginal
    (fun i => limitCanonicalNativeChart (q i)) D hD hDb hcover hsmooth
    g (G.limit.flow.metric t)
  intro i
  apply terminalCommonInterval_original_germ_metric F W history baseTime hbaseTime
    basePoint hPositive hDiverges G P rho hrho (C i) (I i) (U i) (hIc i) (hU i)
    (e i) (aRaw i) t ht ht0 (hI i) (q i) (hD i)
    (g.pullbackCoefficients (aOriginal i).symm)
    (fun x => (extChartAt (𝓡 3) (q i)) (d ((aOriginal i).symm x)))
    (hA i) (fun _ hx => (limitCanonicalNativeChart (q i)).map_source (hDb i hx))
    (hsource i) (hjets i)

end PoincareConjecture.M47
