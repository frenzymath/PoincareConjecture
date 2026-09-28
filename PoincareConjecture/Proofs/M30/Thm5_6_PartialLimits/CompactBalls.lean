import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.MetricComparison
import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.BoundaryCoverage
import PoincareConjecture.Proofs.M13.Length

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology ENNReal Bundle

universe u

namespace PoincareConjecture.M30.PartialPointedMetricConvergence

variable {n : ℕ} {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)]
  [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
  [∀ k, IsManifold (𝓡 n) ∞ (M k)]
  {g : ∀ k, RiemannianMetric n (M k)} {p : ∀ k, M k} {A : ℝ}
  (G : PartialPointedMetricConvergence g p A)

private theorem eventually_pathELength_le {γ : ℝ → G.limitCarrier.carrier}
    (hγ : letI := G.limitCarrier.topologicalSpace
      letI := G.limitCarrier.chartedSpace
      letI := G.limitCarrier.isManifold
      ContMDiffOn 𝓘(ℝ) (𝓡 n) 1 γ (Icc (0 : ℝ) 1)) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ᶠ k in atTop,
      (g (G.subsequence k)).pathELength (G.embedding k ∘ γ) 0 1 ≤
        ENNReal.ofReal (Real.sqrt 2) * G.limitMetric.pathELength γ 0 1 := by
  let : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) G.limitCarrier.carrier :=
    G.limitCarrier.chartedSpace
  let : IsManifold (𝓡 n) ∞ G.limitCarrier.carrier := G.limitCarrier.isManifold
  let K := γ '' Icc (0 : ℝ) 1
  have hK : IsCompact K := isCompact_Icc.image_of_continuousOn hγ.continuousOn
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset hK
  filter_upwards [G.eventually_pullback_inner_le_twice hK, eventually_ge_atTop j]
    with k hk hjk
  rw [M13.pathELength_eq_lintegral_tangentNorm,
    M13.pathELength_eq_lintegral_tangentNorm,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply setLIntegral_mono' measurableSet_Ioo
  intro t ht
  rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg 2)]
  apply ENNReal.ofReal_le_ofReal
  have hγt : γ t ∈ K := mem_image_of_mem γ ⟨ht.1.le, ht.2.le⟩
  have hmap := (G.embedding_smooth k
    ⟨γ t, G.exhaustion_monotone hjk (hj hγt)⟩).contMDiffAt
  have hdiff : MDifferentiableAt 𝓘(ℝ) (𝓡 n) γ t :=
    (hγ.mdifferentiableOn one_ne_zero t ⟨ht.1.le, ht.2.le⟩).mdifferentiableAt
      (Icc_mem_nhds ht.1 ht.2)
  change Real.sqrt _ ≤ Real.sqrt 2 * Real.sqrt _
  rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  apply Real.sqrt_le_sqrt
  rw [mfderiv_comp t (hmap.mdifferentiableAt (by simp)) hdiff]
  exact hk (γ t) hγt (mfderiv 𝓘(ℝ) (𝓡 n) γ t 1)

theorem eventually_mem_ball {r : ℝ} {x : G.limitCarrier.carrier}
    (hx : letI := G.limitCarrier.topologicalSpace
      letI := G.limitCarrier.chartedSpace
      letI := G.limitCarrier.isManifold
      x ∈ G.limitMetric.ball G.base r) :
    ∀ᶠ k in atTop,
      G.embedding k x ∈ (g (G.subsequence k)).ball (p (G.subsequence k)) (2 * r) := by
  let : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) G.limitCarrier.carrier :=
    G.limitCarrier.chartedSpace
  let : IsManifold (𝓡 n) ∞ G.limitCarrier.carrier := G.limitCarrier.isManifold
  obtain ⟨γ, h0, h1, hγ, hlength⟩ := M13.exists_pathELength_lt G.limitMetric hx
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset
    (isCompact_Icc.image_of_continuousOn hγ.continuousOn)
  filter_upwards [G.eventually_pathELength_le hγ, eventually_ge_atTop j] with k hk hjk
  have hf : ContMDiffOn (𝓡 n) (𝓡 n) 1 (G.embedding k) (G.exhaustion k) := by
    intro y hy
    exact ((G.embedding_smooth k ⟨y, hy⟩).contMDiffAt.of_le (by simp)).contMDiffWithinAt
  have hη : ContMDiffOn 𝓘(ℝ) (𝓡 n) 1 (G.embedding k ∘ γ) (Icc (0 : ℝ) 1) :=
    hf.comp hγ (fun t ht => G.exhaustion_monotone hjk (hj (mem_image_of_mem γ ht)))
  have hη0 : (G.embedding k ∘ γ) 0 = p (G.subsequence k) := by
    simpa only [Function.comp_apply, h0] using G.base_preserving k
  have hη1 : (G.embedding k ∘ γ) 1 = G.embedding k x := by
    simp only [Function.comp_apply, h1]
  have hdist := M13.edist_le_pathELength (g (G.subsequence k)) hη hη0 hη1 zero_le_one
  have hsqrt : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsqrt_le : Real.sqrt 2 ≤ 2 := by
    have := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  change _ < ENNReal.ofReal (2 * r)
  calc
    _ ≤ ENNReal.ofReal (Real.sqrt 2) * G.limitMetric.pathELength γ 0 1 := hdist.trans hk
    _ < ENNReal.ofReal (Real.sqrt 2) * ENNReal.ofReal r :=
      (ENNReal.mul_lt_mul_right (ne_of_gt (ENNReal.ofReal_pos.mpr hsqrt))
        ENNReal.ofReal_ne_top) hlength
    _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal r :=
      mul_le_mul' (ENNReal.ofReal_le_ofReal hsqrt_le) le_rfl
    _ = ENNReal.ofReal (2 * r) := (ENNReal.ofReal_mul (by norm_num)).symm

theorem ball_subset_exhaustion_of_source_ball_coverage {r : ℝ} {l : ℕ}
    (hcover : ∀ᶠ k in atTop,
      (g (G.subsequence k)).ball (p (G.subsequence k)) (2 * r) ⊆
        G.embedding k '' G.exhaustion l) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    G.limitMetric.ball G.base r ⊆ G.exhaustion l := by
  let : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) G.limitCarrier.carrier :=
    G.limitCarrier.chartedSpace
  let : IsManifold (𝓡 n) ∞ G.limitCarrier.carrier := G.limitCarrier.isManifold
  intro x hx
  obtain ⟨i, hi⟩ := G.exists_exhaustion_superset (K := {x}) isCompact_singleton
  have hxstage : x ∈ G.exhaustion i := hi (mem_singleton x)
  obtain ⟨k, hkcover, hkball, hlk, hik⟩ :=
    (hcover.and ((G.eventually_mem_ball hx).and
      ((eventually_ge_atTop l).and (eventually_ge_atTop i)))).exists
  obtain ⟨y, hy, heq⟩ := hkcover hkball
  have hyx : y = x := congrArg Subtype.val ((G.embedding_open k).injective
    (a₁ := ⟨y, G.exhaustion_monotone hlk hy⟩)
    (a₂ := ⟨x, G.exhaustion_monotone hik hxstage⟩) heq)
  simpa only [hyx] using hy

theorem isCompact_closure_ball [∀ k, T2Space (M k)] {r : ℝ}
    (hr : 0 < r) (hrA : 2 * r < A) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    IsCompact (closure (G.limitMetric.ball G.base r)) := by
  let : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) G.limitCarrier.carrier :=
    G.limitCarrier.chartedSpace
  let : IsManifold (𝓡 n) ∞ G.limitCarrier.carrier := G.limitCarrier.isManifold
  let : T2Space G.limitCarrier.carrier := G.limitCarrier.t2Space
  obtain ⟨l, hl⟩ := G.source_ball_coverage (by positivity : 0 < 2 * r) hrA
  exact (G.exhaustion_compactClosure l).of_isClosed_subset isClosed_closure
    (closure_mono (G.ball_subset_exhaustion_of_source_ball_coverage hl))

end PoincareConjecture.M30.PartialPointedMetricConvergence
