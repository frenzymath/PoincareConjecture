import PoincareLib.Geometry.RicciFlow.Blowup.Construction.PartialLimits.ExpandingNormalConvergence
import PoincareLib.Geometry.RicciFlow.Compactness.Coordinates.DiagonalCovering
import PoincareLib.Geometry.RicciFlow.Compactness.Subsequence

/-!
# Complete reference convergence from expanding-time bounds

The reference compactness hypotheses construct the normal covers used for
one retained open-time limit. The original sequence and all comparison maps
are kept by composing the selected indices. This is Morgan--Tian Definition
5.12, Proposition 5.14 and Theorem 5.15, pp. 90-92, applied in Theorem 11.8,
pp. 272-279.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareMT.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold

/-- Construct the normal covers and retain the limit on the full open time
domain, as in Morgan--Tian Definition 5.12, Proposition 5.14 and Theorem 5.15,
pp. 90-92, and Theorem 11.8, pp. 272-279. -/
theorem exists_complete_reference_convergence_of_expanding_bounds
    {n : ℕ} {s' s : ℝ} (hn : 1 ≤ n)
    (Href : PointedRicciFlowCompactnessHypotheses n s' s)
    (hShi : LocalCurvatureDerivativeEstimates.{0})
    {J : ℕ → Set ℝ}
    (Fseq : ∀ k, RicciFlow n (Href.sequence.carrier k).carrier (J k))
    (hmetric : ∀ k, (Fseq k).metric = (Href.sequence.flow k).flow.metric)
    {W : Set ℝ} (hW : IsOpen W) (hWord : W.OrdConnected)
    (hwindow : Ioo s' s ⊆ W)
    (htime : ∀ a b : ℝ, Icc a b ⊆ W → ∀ᶠ k in atTop, Icc a b ⊆ J k)
    (hcurv : ∀ a b : ℝ, Icc a b ⊆ W →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k in atTop,
        ∀ t ∈ Icc a b, ∀ x : (Href.sequence.carrier k).carrier,
          ((Fseq k).connection t).curvatureTensorNorm x ≤ C) :
    ∃ G : PointedGeometricConvergence Href.sequence,
      letI : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) G.limitCarrier.carrier :=
        G.limitCarrier.chartedSpace
      letI : IsManifold (𝓡 n) ∞ G.limitCarrier.carrier := G.limitCarrier.isManifold
      ∃ F : RicciFlow n G.limitCarrier.carrier W,
        F.metric = G.limitFlow.flow.metric ∧
        G.limitCarrier.metricComplete (F.metric 0) ∧
        ∀ q' : G.limitCarrier.carrier, ∀ m : ℕ,
          ∀ K : Set (ℝ × EuclideanSpace ℝ (Fin n)), IsCompact K →
          K ⊆ W ×ˢ (extChartAt (𝓡 n) q').target → TendstoUniformlyOn
            (fun k => iteratedFDeriv ℝ m
              (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
                ((Fseq (G.subsequence k)).metric z.1).pullbackCoefficients
                  ((fun x => ((G.embedding k).toFun (0, x)).2) ∘
                    (extChartAt (𝓡 n) q').symm) z.2))
            (iteratedFDeriv ℝ m
              (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
                (F.metric z.1).pullbackCoefficients
                  (extChartAt (𝓡 n) q').symm z.2)) atTop K := by
  classical
  obtain ⟨σ, hσ, R, ρ, a, b, N, hparams, hcovers⟩ :=
    Href.exists_diagonal_normalChartCovers hn
  let Hsub := Href.subsequence σ hσ
  let Fsub : ∀ k, RicciFlow n (Hsub.sequence.carrier k).carrier (J (σ k)) :=
    fun k => Fseq (σ k)
  have hmetricSub : ∀ k, (Fsub k).metric = (Hsub.sequence.flow k).flow.metric :=
    fun k => hmetric (σ k)
  have htimeSub : ∀ a b : ℝ, Icc a b ⊆ W →
      ∀ᶠ k in atTop, Icc a b ⊆ J (σ k) := by
    intro a b hab
    exact hσ.tendsto_atTop.eventually (htime a b hab)
  have hcurvSub : ∀ a b : ℝ, Icc a b ⊆ W →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k in atTop,
        ∀ t ∈ Icc a b, ∀ x : (Hsub.sequence.carrier k).carrier,
          ((Fsub k).connection t).curvatureTensorNorm x ≤ C := by
    intro a b hab
    obtain ⟨C, hC, hbound⟩ := hcurv a b hab
    exact ⟨C, hC, hσ.tendsto_atTop.eventually hbound⟩
  let cover : ∀ k j, j ≤ k →
      NormalChartCover (Hsub.sequence.flow k).flow.metric
        (Hsub.sequence.flow k).base s' s ((j : ℝ) + 1)
        (R j) (ρ j) (a j) (b j) (N j) :=
    fun k j hjk => (hcovers k j hjk).choose
  obtain ⟨Gsub, F, hF, hcomplete, hjets⟩ :=
    exists_complete_reference_convergence_of_expanding_normal_charts
      Hsub hShi Fsub hmetricSub hW hWord hwindow htimeSub hcurvSub cover
      (fun j => (hparams j).1) (fun j => (hparams j).2.1)
      (fun j => (hparams j).2.2.1) (fun j => (hparams j).2.2.2)
  exact ⟨Gsub.ofSubsequence hσ, F, hF, hcomplete, hjets⟩

end PoincareMT.M30
