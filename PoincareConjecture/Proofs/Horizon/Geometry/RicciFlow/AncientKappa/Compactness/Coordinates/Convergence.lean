import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Ancient.Pointed
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.MetricFamily.PullbackCoefficients













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold



theorem contDiffAt_spatialPullback_coordinateCoefficient
    {n : ℕ} (L C : FlowCarrier.{0} n) {g : ℝ → C.metric} {J : Set ℝ}
    (hg : RiemannianMetric.IsSmoothFamilyOn g J) (hJ : IsOpen J)
    {e : L.carrier → C.carrier} {U : Set L.carrier}
    (hU : IsOpen U) (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e U)
    (q : L.carrier) (a b : Fin n) (p : ℝ × EuclideanSpace ℝ (Fin n))
    (ht : p.1 ∈ J)
    (hp : p.2 ∈ (extChartAt (𝓡 n) q).target ∧
      (extChartAt (𝓡 n) q).symm p.2 ∈ U) :
    ContDiffAt ℝ ∞ (L.coordinateCoefficient q
      (fun t x v w => spatialPullbackInner L C (g t) e x v w) a b) p := by
  let c := extChartAt (𝓡 n) q
  have hc {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ c.target) :
      ContMDiffAt (𝓡 n) (𝓡 n) ∞ c.symm x :=
    (contMDiffWithinAt_extChartAt_symm_target (n := ∞) q hx).contMDiffAt
      (extChartAt_target_mem_nhds' hx)
  have heAt {x : L.carrier} (hx : x ∈ U) : ContMDiffAt (𝓡 n) (𝓡 n) ∞ e x :=
    he.contMDiffAt (hU.mem_nhds hx)
  have hcomp : ContMDiffAt (𝓡 n) (𝓡 n) ∞ (e ∘ c.symm) p.2 :=
    (heAt hp.2).comp p.2 (hc hp.1)
  have hs := ((hg.contDiffAt_spacetime_pullbackCoefficients hJ hcomp ht).clm_apply
    (contDiffAt_const (c := EuclideanSpace.basisFun (Fin n) ℝ a))).clm_apply
      (contDiffAt_const (c := EuclideanSpace.basisFun (Fin n) ℝ b))
  apply hs.congr_of_eventuallyEq
  have htarget := continuousAt_snd.preimage_mem_nhds (extChartAt_target_mem_nhds' hp.1)
  have hdomain := ((hc hp.1).continuousAt.comp continuousAt_snd).preimage_mem_nhds
    (hU.mem_nhds hp.2)
  filter_upwards [htarget, hdomain] with z hz hzU
  have hderiv := mfderiv_comp z.2 ((heAt hzU).mdifferentiableAt (by simp))
    ((hc hz).mdifferentiableAt (by simp))
  change (g z.1).inner (e (c.symm z.2))
      (mfderiv (𝓡 n) (𝓡 n) e (c.symm z.2)
        (mfderiv (𝓡 n) (𝓡 n) c.symm z.2 (EuclideanSpace.basisFun (Fin n) ℝ a)))
      (mfderiv (𝓡 n) (𝓡 n) e (c.symm z.2)
        (mfderiv (𝓡 n) (𝓡 n) c.symm z.2 (EuclideanSpace.basisFun (Fin n) ℝ b))) =
    (g z.1).inner (e (c.symm z.2))
      (mfderiv (𝓡 n) (𝓡 n) (e ∘ c.symm) z.2 (EuclideanSpace.basisFun (Fin n) ℝ a))
      (mfderiv (𝓡 n) (𝓡 n) (e ∘ c.symm) z.2 (EuclideanSpace.basisFun (Fin n) ℝ b))
  rw [hderiv]
  rfl



theorem contDiffAt_coordinateCoefficient_of_smoothFamily
    {n : ℕ} (C : FlowCarrier.{0} n) {g : ℝ → C.metric} {J : Set ℝ}
    (hg : RiemannianMetric.IsSmoothFamilyOn g J) (hJ : IsOpen J)
    (q : C.carrier) (a b : Fin n) (p : ℝ × EuclideanSpace ℝ (Fin n))
    (ht : p.1 ∈ J) (hp : p.2 ∈ (extChartAt (𝓡 n) q).target) :
    ContDiffAt ℝ ∞ (C.coordinateCoefficient q
      (fun t x v w => C.metricInner (g t) x v w) a b) p := by
  simpa only [spatialPullbackInner, id_eq, mfderiv_id, ContinuousLinearMap.id_apply,
    FlowCarrier.metricInner] using
    contDiffAt_spatialPullback_coordinateCoefficient C C hg hJ
      (e := id) isOpen_univ contMDiffOn_id q a b p ht ⟨hp, mem_univ _⟩

namespace AncientPointedGeometricConvergence

variable {n : ℕ} {C : ℕ → FlowCarrier.{0} n} {g : ∀ k, ℝ → (C k).metric}
  {p : ∀ k, (C k).carrier} {T : ℝ}
  (G : AncientPointedGeometricConvergence C g p T)



theorem pullback_metric_CInfinity_within_Icc
    (hg : ∀ k, RiemannianMetric.IsSmoothFamilyOn (g k) (Iio T))
    (l u : ℝ) (hlu : l < u) (huT : u < T)
    (q : G.limitCarrier.carrier) (j r : ℕ)
    (K : Set (ℝ × EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hKU : K ⊆ {z | z.1 ∈ Icc l u ∧ z.2 ∈ (extChartAt (𝓡 n) q).target ∧
      (extChartAt (𝓡 n) q).symm z.2 ∈ G.exhaustion j})
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, j ≤ N ∧ ∀ k ≥ N, ∀ a b : Fin n, ∀ z ∈ K,
      ‖iteratedFDerivWithin ℝ r
          (G.limitCarrier.coordinateCoefficient q
            (fun t x v w => spatialPullbackInner G.limitCarrier (C (G.subsequence k))
              (g (G.subsequence k) t) (G.embedding k) x v w) a b)
          (Icc l u ×ˢ Set.univ) z -
        iteratedFDerivWithin ℝ r
          (G.limitCarrier.coordinateCoefficient q
            (fun t x v w => G.limitCarrier.metricInner (G.limitFlow.metric t) x v w) a b)
          (Icc l u ×ˢ Set.univ) z‖ < ε := by
  have hpast : K ⊆ {z | z.1 ∈ Iio T ∧ z.2 ∈ (extChartAt (𝓡 n) q).target ∧
      (extChartAt (𝓡 n) q).symm z.2 ∈ G.exhaustion j} := by
    intro z hz
    exact ⟨(hKU hz).1.2.trans_lt huT, (hKU hz).2⟩
  obtain ⟨N, hjN, hN⟩ := G.pullback_metric_CInfinity q j r K hK hpast ε hε
  refine ⟨N, hjN, ?_⟩
  intro k hk a b z hz
  have hmono : Monotone G.exhaustion := monotone_nat_of_le_succ G.exhaustion_increasing
  have hxk : (extChartAt (𝓡 n) q).symm z.2 ∈ G.exhaustion k :=
    hmono (hjN.trans hk) (hKU hz).2.2
  have hsource := contDiffAt_spatialPullback_coordinateCoefficient
    G.limitCarrier (C (G.subsequence k)) (hg (G.subsequence k)) isOpen_Iio
    (G.exhaustion_open k) (fun x hx =>
      (G.embedding_smooth k ⟨x, hx⟩).contMDiffAt.contMDiffWithinAt)
    q a b z (hpast hz).1 ⟨(hKU hz).2.1, hxk⟩
  have hlimit := contDiffAt_coordinateCoefficient_of_smoothFamily G.limitCarrier
    G.limitFlow.smooth isOpen_Iio q a b z (hpast hz).1 (hKU hz).2.1
  have hdiff : UniqueDiffOn ℝ (Icc l u ×ˢ (univ : Set (EuclideanSpace ℝ (Fin n)))) :=
    (uniqueDiffOn_Icc hlu).prod uniqueDiffOn_univ
  have hmem : z ∈ Icc l u ×ˢ (univ : Set (EuclideanSpace ℝ (Fin n))) :=
    ⟨(hKU hz).1, mem_univ _⟩
  have hr : (r : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr (le_top : (r : ℕ∞) ≤ ⊤)
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hdiff (hsource.of_le hr) hmem,
    iteratedFDerivWithin_eq_iteratedFDeriv hdiff (hlimit.of_le hr) hmem]
  exact hN k hk a b z hz

end AncientPointedGeometricConvergence

end PoincareConjecture
