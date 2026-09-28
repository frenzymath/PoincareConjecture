import PoincareConjecture.Proofs.M47.TerminalCommonIntervalOriginalGermGlobalization
import PoincareConjecture.Proofs.M47.TerminalGermsExhaustionFlows










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
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

private local instance originalExhaustionTopology : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance originalExhaustionCharts : ChartedSpace E G.limit.carrier.carrier :=
  G.limit.carrier.chartedSpace
private local instance originalExhaustionManifold : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier :=
  G.limit.carrier.isManifold




theorem terminalCommonInterval_original_exhaustion_identification
    (P : M47Predecessors.{u}) (rho : ℕ → ℕ) (hrho : StrictMono rho)
    {ι : Type*} {Piece : ι → Type v} {M : Type v}
    [∀ i, TopologicalSpace (Piece i)] [TopologicalSpace M]
    [∀ i, ChartedSpace E (Piece i)] [ChartedSpace E M]
    [∀ i, IsManifold (𝓡 3) ∞ (Piece i)] [IsManifold (𝓡 3) ∞ M]
    (g : ∀ i, RiemannianMetric 3 (Piece i))
    (q : ∀ i, Piece i → M)
    (hq : ∀ i, IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (q i))
    (U : Opens M) (gU : RiemannianMetric 3 U)
    (hcover : ∀ y ∈ U, ∃ i x, q i x = y)
    (hread : ∀ i (x : Piece i) (hx : q i x ∈ U) (a b : TangentSpace (𝓡 3) x),
      (g i).inner x a b = gU.inner ⟨q i x, hx⟩
        (mfderiv (𝓡 3) (𝓡 3) (q i) x a) (mfderiv (𝓡 3) (𝓡 3) (q i) x b))
    (d : Diffeomorph (𝓡 3) (𝓡 3) M G.limit.sliceCarrier.carrier ∞)
    (aOriginal : ∀ i, ℕ → PartialDiffeomorph (𝓡 3) (𝓡 3) (Piece i) E ∞)
    (native : ι → ℕ → G.limit.sliceCarrier.carrier)
    (D : ι → ℕ → Set E) (hD : ∀ i j, IsOpen (D i j))
    (hDb : ∀ i j, MapsTo (fun x => d (q i ((aOriginal i j).symm x))) (D i j)
      (extChartAt (𝓡 3) (native i j)).source)
    (hchartCover : ∀ i (x : Piece i),
      ∃ j, x ∈ (aOriginal i j).source ∧ aOriginal i j x ∈ D i j)
    (hsmooth : ∀ i j, ContDiffOn ℝ ∞
      (fun x => (extChartAt (𝓡 3) (native i j))
        (d (q i ((aOriginal i j).symm x)))) (D i j))
    (C : ι → ℕ → ℕ → GeneralizedSliceCarrier.{u}) (I : ι → ℕ → ℕ → Set ℝ)
    (space : ∀ i j n, Set (C i j n).carrier) (hIc : ∀ i j n, (I i j n).OrdConnected)
    (hspace : ∀ i j n, IsOpen (space i j n))
    (e : ∀ i j n, GeneralizedFlowCylinder (history (G.subsequence (rho n))).generalized
      (C i j n) (baseTime (G.subsequence (rho n))) ((V).scale (G.subsequence (rho n)))
      (I i j n) (space i j n))
    (aRaw : ∀ i j n, PartialDiffeomorph (𝓡 3) (𝓡 3) (C i j n).carrier E ∞)
    (t : ℝ) (ht : t ∈ J) (ht0 : t ≤ 0) (hI : ∀ i j n, Icc t 0 ⊆ I i j n)
    (hA : ∀ i j x, x ∈ D i j → ∀ v w : E, Tendsto (fun n =>
      (V).scale (G.subsequence (rho n)) *
        ((history (G.subsequence (rho n))).generalized.metric
          (baseTime (G.subsequence (rho n)) +
            t / (V).scale (G.subsequence (rho n)))).pullbackCoefficients
          ((e i j n).forward t (hI i j n ⟨le_rfl, ht0⟩) ∘ (aRaw i j n).symm) x v w)
      atTop (𝓝 ((g i).pullbackCoefficients (aOriginal i j).symm x v w))) :
    let Tn := fun i j n =>
      (((aRaw i j n).symm.toOpenPartialHomeomorph.trans
        ((e i j n).spatialOpenPartialHomeomorph (hspace i j n) 0
          (hI i j n ⟨ht0, le_rfl⟩))).trans
            ((G.embedding (rho n)).spatialOpenPartialHomeomorph
              (G.exhaustion.space_open (rho n)) 0
              ⟨neg_nonpos.mpr (G.exhaustion.time_pos (rho n)).le, le_rfl⟩).symm).trans
                (limitCanonicalNativeChart (native i j)).toOpenPartialHomeomorph
    (∀ i j x, x ∈ D i j → ∀ᶠ n in atTop, x ∈ (Tn i j n).source) →
    (∀ i j m K, IsCompact K → K ⊆ D i j → TendstoUniformlyOn
      (fun n => iteratedFDeriv ℝ m (Tn i j n))
      (iteratedFDeriv ℝ m (fun x => (extChartAt (𝓡 3) (native i j))
        (d (q i ((aOriginal i j).symm x))))) atTop K) →
    ∀ y : U, ∀ v w : TangentSpace (𝓡 3) y,
      gU.inner y v w = (G.limit.flow.metric t).inner (d y.val)
        (mfderiv (𝓡 3) (𝓡 3) d y.val v) (mfderiv (𝓡 3) (𝓡 3) d y.val w) := by
  dsimp only
  intro hsource hjets
  have hident (i : ι) := terminalCommonInterval_original_germ_identification
    F W history baseTime hbaseTime basePoint hPositive hDiverges G P rho hrho
    (g i) ((d : M → G.limit.sliceCarrier.carrier) ∘ q i)
    (aOriginal i) (native i) (D i) (hD i) (hDb i) (hchartCover i) (hsmooth i)
    (C i) (I i) (space i) (hIc i) (hspace i) (e i) (aRaw i)
    t ht ht0 (hI i) (hA i) (hsource i) (hjets i)
  intro y v w
  obtain ⟨i, x, hx⟩ := hcover y.val y.property
  have hxU : q i x ∈ U := by rw [hx]; exact y.property
  let L := (hq i).mfderivToContinuousLinearEquiv (by simp) x
  let a := L.symm v
  let b := L.symm w
  have ha : mfderiv (𝓡 3) (𝓡 3) (q i) x a = v := L.apply_symm_apply _
  have hb : mfderiv (𝓡 3) (𝓡 3) (q i) x b = w := L.apply_symm_apply _
  have hxy : (⟨q i x, hxU⟩ : U) = y := Subtype.ext hx
  have hleft : (g i).inner x a b = gU.inner y v w := by
    calc
      _ = gU.inner ⟨q i x, hxU⟩ _ _ := hread i x hxU a b
      _ = gU.inner y (mfderiv (𝓡 3) (𝓡 3) (q i) x a)
          (mfderiv (𝓡 3) (𝓡 3) (q i) x b) := congrArg
        (fun z : U => gU.inner z (mfderiv (𝓡 3) (𝓡 3) (q i) x a)
          (mfderiv (𝓡 3) (𝓡 3) (q i) x b)) hxy
      _ = _ := congrArg₂ (fun v w : E => gU.inner y v w) ha hb
  have hright := hident i x a b
  rw [mfderiv_comp x (d.mdifferentiable (by simp) (q i x))
    ((hq i).contMDiff.mdifferentiable (by simp) x)] at hright
  have hright' : (g i).inner x a b = (G.limit.flow.metric t).inner (d (q i x))
      (mfderiv (𝓡 3) (𝓡 3) d (q i x) v) (mfderiv (𝓡 3) (𝓡 3) d (q i x) w) := by
    simpa only [ContinuousLinearMap.comp_apply, ha, hb, Function.comp_apply] using hright
  exact hleft.symm.trans (hright'.trans (congrArg
    (fun z : M => (G.limit.flow.metric t).inner (d z)
      (mfderiv (𝓡 3) (𝓡 3) d z v) (mfderiv (𝓡 3) (𝓡 3) d z w)) hx))

end PoincareConjecture.M47
