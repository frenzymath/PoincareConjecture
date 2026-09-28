import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.FlowConvergence
import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.MetricComparison
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Annular.SpacetimeBounds
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.UniformSpace.UniformConvergence


















set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle

universe u

namespace PoincareConjecture.M30.PartialPointedFlowConvergence





theorem tendstoUniformlyOn_scalar_metric_jets
    {n : ℕ} {M : ℕ → Type u}
    [∀ k, TopologicalSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    {J : Set ℝ} {F : ∀ k, RicciFlow n (M k) J}
    {p : ∀ k, M k} {A t₀ : ℝ}
    (G : PartialPointedFlowConvergence F p A t₀) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ (q : G.limitCarrier.carrier) (m : ℕ)
      (K : Set (ℝ × EuclideanSpace ℝ (Fin n))),
      IsCompact K → K ⊆ J ×ˢ (extChartAt (𝓡 n) q).target →
      ∀ a b : Fin n,
        TendstoUniformlyOn
          (fun j => iteratedFDerivWithin ℝ m
            (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
              ((F (G.subsequence j)).metric z.1).pullbackCoefficients
                (G.embedding j ∘ (extChartAt (𝓡 n) q).symm) z.2
                (EuclideanSpace.basisFun (Fin n) ℝ a)
                (EuclideanSpace.basisFun (Fin n) ℝ b))
            (J ×ˢ (extChartAt (𝓡 n) q).target))
          (iteratedFDerivWithin ℝ m
            (G.limitCarrier.coordinateCoefficient q
              (fun t x v w => (G.limitFlow.metric t).inner x v w) a b)
            (J ×ˢ (extChartAt (𝓡 n) q).target)) atTop K := by
  let : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) G.limitCarrier.carrier :=
    G.limitCarrier.chartedSpace
  let : IsManifold (𝓡 n) ∞ G.limitCarrier.carrier := G.limitCarrier.isManifold
  intro q m K hK hKS a b
  let V := EuclideanSpace ℝ (Fin n)
  let : NormedAddCommGroup (V →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedAddCommGroup (V →L[ℝ] V →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let E := ℝ × V
  let B := V →L[ℝ] V →L[ℝ] ℝ
  let c := extChartAt (𝓡 n) q
  let S := J ×ˢ c.target
  let f : ℕ → E → B := fun j z =>
    ((F (G.subsequence j)).metric z.1).pullbackCoefficients (G.embedding j ∘ c.symm) z.2
  let f₀ : E → B := fun z => (G.limitFlow.metric z.1).pullbackCoefficients c.symm z.2
  have hconvex : Convex ℝ J := G.limitFlow.interval.convex
  have hJ : UniqueDiffOn ℝ J := uniqueDiffOn_convex hconvex
    (hconvex.nontrivial_iff_nonempty_interior.mp G.limitFlow.nontrivial)
  have hS : UniqueDiffOn ℝ S := hJ.prod (isOpen_extChartAt_target (I := 𝓡 n) q).uniqueDiffOn
  have hc (z : V) (hz : z ∈ c.target) : ContMDiffAt (𝓡 n) (𝓡 n) ∞ c.symm z :=
    (contMDiffOn_extChartAt_symm q).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 n) q).mem_nhds hz)
  have hmap : ContinuousOn (fun z : E => c.symm z.2) K := by
    intro z hz
    exact ((hc z.2 (hKS hz).2).continuousAt.comp continuousAt_snd).continuousWithinAt
  obtain ⟨j₀, hj₀⟩ := G.toPartialPointedMetricConvergence.exists_exhaustion_superset
    (hK.image_of_continuousOn hmap)
  have hsource : ∀ᶠ j in atTop, ∀ z ∈ K, ContDiffWithinAt ℝ ∞ (f j) S z := by
    filter_upwards [eventually_ge_atTop j₀] with j hj z hz
    have hx : c.symm z.2 ∈ G.exhaustion j :=
      G.toPartialPointedMetricConvergence.exhaustion_monotone hj
        (hj₀ (mem_image_of_mem _ hz))
    have ha := (G.embedding_smooth j ⟨c.symm z.2, hx⟩).contMDiffAt
    have hcomp := ha.comp z.2 (hc z.2 (hKS hz).2)
    exact ((F (G.subsequence j)).smooth.contDiffWithinAt_spacetime_pullbackCoefficients
      hcomp (hKS hz).1).mono (prod_mono subset_rfl (subset_univ _))
  have hlimit (z : E) (hz : z ∈ K) : ContDiffWithinAt ℝ ∞ f₀ S z :=
    (G.limitFlow.smooth.contDiffWithinAt_spacetime_pullbackCoefficients
      (hc z.2 (hKS hz).2) (hKS hz).1).mono (prod_mono subset_rfl (subset_univ _))
  let L : B →L[ℝ] ℝ :=
    (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.basisFun (Fin n) ℝ b)).comp
      (ContinuousLinearMap.apply ℝ (V →L[ℝ] ℝ) (EuclideanSpace.basisFun (Fin n) ℝ a))
  let Lm := ContinuousLinearMap.compContinuousMultilinearMapL ℝ
    (fun _ : Fin m => E) B ℝ L
  have hjets : TendstoUniformlyOn
      (fun j => iteratedFDerivWithin ℝ m (f j) S)
      (iteratedFDerivWithin ℝ m f₀ S) atTop K := G.spacetime_metric_jets q m K hK hKS
  have heval := Lm.uniformContinuous.comp_tendstoUniformlyOn hjets
  change TendstoUniformlyOn
    (fun j => iteratedFDerivWithin ℝ m (L ∘ f j) S)
    (iteratedFDerivWithin ℝ m (L ∘ f₀) S) atTop K
  have hm : (m : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr (le_top : (m : ℕ∞) ≤ ⊤)
  refine (heval.congr ?_).congr_right ?_
  · filter_upwards [hsource] with j hj z hz
    exact (L.iteratedFDerivWithin_comp_left (hj z hz) hS (hKS hz) hm).symm
  · intro z hz
    exact (L.iteratedFDerivWithin_comp_left (hlimit z hz) hS (hKS hz) hm).symm

end PoincareConjecture.M30.PartialPointedFlowConvergence
