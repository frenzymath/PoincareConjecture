import PoincareConjecture.Proofs.M47.LimitCanonicalRoundControl
import PoincareConjecture.Proofs.M47.LimitNoncollapsePhysicalTime









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {V : GeneralizedBlowupSequence.{u}} {J : Set ℝ}

private local instance (G : GeneralizedBlowupConvergence V J) :
    TopologicalSpace G.limit.carrier.carrier := G.limit.carrier.topologicalSpace
private local instance (G : GeneralizedBlowupConvergence V J) :
    ChartedSpace E3 G.limit.carrier.carrier := G.limit.carrier.chartedSpace
private local instance (G : GeneralizedBlowupConvergence V J) :
    IsManifold (𝓡 3) ∞ G.limit.carrier.carrier := G.limit.carrier.isManifold



theorem limitCanonical_eventually_physical_round_comparison
    (P : M47Predecessors.{u})
    (G : GeneralizedBlowupConvergence V J)
    (hcompact : IsCompact (univ : Set G.limit.sliceCarrier.carrier))
    (F : ℕ → SurgeryFlowData.{u})
    (R : ∀ i, M33RegularHistoryRealization (V.flow i) (F i))
    {X : Type u} [TopologicalSpace X] [ChartedSpace E3 X]
    [IsManifold (𝓡 3) ∞ X] [CompactSpace X]
    (gR : RiemannianMetric 3 X) (DR : LeviCivitaData gR)
    {i : X → G.limit.sliceCarrier.carrier}
    (hi : ContMDiff (𝓡 3) (𝓡 3) ∞ i)
    (c : ℝ) (m : ℕ) {epsilon : ℝ}
    (hold : ∃ b : ℝ, b < epsilon ^ 2 ∧ ∀ x : X,
      singularMetricJetErrorSquared gR DR
        (fun y v => c * (G.limit.flow.metric 0).inner (i y)
          (mfderiv (𝓡 3) (𝓡 3) i y (v 0))
          (mfderiv (𝓡 3) (𝓡 3) i y (v 1))) m x ≤ b) :
    ∃ bound : ℝ, bound < epsilon ^ 2 ∧
      ∀ᶠ k in atTop,
        ∃ ht : (V.base (G.subsequence k)).1 +
            0 / V.scale (G.subsequence k) ∈
              (V.flow (G.subsequence k)).interval,
          let hzero : 0 ∈ Icc (-G.exhaustion.time k) 0 :=
            ⟨neg_nonpos.mpr (G.exhaustion.time_pos k).le, le_rfl⟩
          let e := G.embedding k
          let f := limitCanonicalPhysicalChart e (G.exhaustion.space_open k)
            (R (G.subsequence k)) 0 hzero ht
          f.source = univ ∧
          limitCanonicalRoundSourceTensor e i 0 hzero c =
            (fun y : X => fun v => (c * V.scale (G.subsequence k)) *
              singularMetricPullback
                ((F (G.subsequence k)).metric
                  ((V.base (G.subsequence k)).1 +
                    0 / V.scale (G.subsequence k)))
                (f ∘ i) y v) ∧
          (∀ x : X,
            singularMetricJetErrorSquared gR DR
              (fun y : X => fun v => (c * V.scale (G.subsequence k)) *
                singularMetricPullback
                  ((F (G.subsequence k)).metric
                    ((V.base (G.subsequence k)).1 +
                      0 / V.scale (G.subsequence k)))
                  (f ∘ i) y v) m x ≤ bound) ∧
          (⟨(V.base (G.subsequence k)).1 +
              0 / V.scale (G.subsequence k), f G.limit.base⟩ :
              (t : ℝ) × ((F (G.subsequence k)).slice t).carrier) =
            ⟨(e.pointMap 0 hzero G.limit.base).1,
              (R (G.subsequence k)).forward
                (e.pointMap 0 hzero G.limit.base).1 ht
                (e.pointMap 0 hzero G.limit.base).2⟩ := by
  obtain ⟨bound, hbound, hcompare⟩ := limitCanonical_round_comparison_bound P G
    hcompact gR DR hi c m hold
  refine ⟨bound, hbound, ?_⟩
  filter_upwards [hcompare,
    limitCanonical_eventually_exhaustion_univ G hcompact] with k hk hfull
  have hzero : 0 ∈ Icc (-G.exhaustion.time k) 0 :=
    ⟨neg_nonpos.mpr (G.exhaustion.time_pos k).le, le_rfl⟩
  have ht : (V.base (G.subsequence k)).1 +
      0 / V.scale (G.subsequence k) ∈
      (V.flow (G.subsequence k)).interval :=
    limitNoncollapse_physical_time_mem G k 0 hzero
  let e := G.embedding k
  let f := limitCanonicalPhysicalChart e (G.exhaustion.space_open k)
    (R (G.subsequence k)) 0 hzero ht
  have hsource : f.source = univ := by
    exact (limitCanonicalPhysicalChart_source e (G.exhaustion.space_open k)
      (R (G.subsequence k)) 0 hzero ht).trans hfull
  have hf : ContMDiff (𝓡 3) (𝓡 3) ∞ f :=
    contMDiffOn_univ.mp (hsource ▸ f.contMDiffOn_toFun)
  have htensor : limitCanonicalRoundSourceTensor e i 0 hzero c =
      (fun y : X => fun v => (c * V.scale (G.subsequence k)) *
        singularMetricPullback
          ((F (G.subsequence k)).metric
            ((V.base (G.subsequence k)).1 +
              0 / V.scale (G.subsequence k)))
          (f ∘ i) y v) := by
    funext y v
    unfold limitCanonicalRoundSourceTensor singularMetricPullback
    rw [mfderiv_comp y (hf.mdifferentiableAt (by simp))
      (hi.mdifferentiableAt (by simp))]
    rw [mul_assoc]
    exact congrArg (c * ·)
      (limitCanonicalPhysicalChart_metric e (G.exhaustion.space_open k)
        (R (G.subsequence k)) 0 hzero ht (hfull ▸ mem_univ (i y))
        (mfderiv (𝓡 3) (𝓡 3) i y (v 0))
        (mfderiv (𝓡 3) (𝓡 3) i y (v 1))).symm
  have hpoint := limitCanonicalPhysicalChart_point_identity e
    (G.exhaustion.space_open k) (R (G.subsequence k)) 0 hzero ht
    G.limit.base (e.pointMap 0 hzero G.limit.base) ht rfl
  refine ⟨ht, ?_⟩
  dsimp only
  refine ⟨hsource, htensor, ?_, hpoint⟩
  intro x
  rw [← htensor]
  exact hk x

end PoincareConjecture.M47
