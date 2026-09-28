import PoincareConjecture.Proofs.M46.Sec16_1_Attainment.SquareModulus
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.UniformSpace.Compact











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Manifold
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.Proofs.M46

variable {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} (G : GeneralizedLGeometryTransport 3 X time I)





theorem exists_compact_crossing_neighborhood {K : Set G.Point} (hK : IsCompact K)
    {D H : ℝ} (hD : 0 ≤ D) (hH : 0 ≤ H) :
    ∃ N : Set G.Point, IsCompact N ∧ K ⊆ interior N ∧
      ∃ delta : ℝ, 0 < delta ∧
        ∀ (T tau : ℝ) (x y : G.Point) (p : M14BackwardPath G T 0 tau x y),
          tau ≤ H →
          IntervalIntegrable (M14.pathSquareKinetic p) volume 0 (Real.sqrt tau) →
          (∫ s in 0..Real.sqrt tau, M14.pathSquareKinetic p s) ≤ D →
          ∀ a ∈ Icc 0 tau, ∀ b ∈ Icc 0 tau,
            |b - a| < delta → p.curve a ∈ K → p.curve b ∈ N := by
  let : Bundle.RiemannianBundle (TangentSpace (spacetimeModel 3) : G.Point → Type _) :=
    ⟨(M14.auxiliarySpacetimeMetric G.spacetime).toRiemannianMetric⟩
  let : EMetricSpace G.Point := .ofRiemannianMetric (spacetimeModel 3) G.Point
  let : LocallyCompactSpace G.Point :=
    Manifold.locallyCompact_of_finiteDimensional (M := G.Point) (spacetimeModel 3)
  obtain ⟨N, hN, hKN⟩ := exists_compact_superset hK
  obtain ⟨epsilon, hepsilon, hball⟩ := lebesgue_number_lemma_of_emetric_nhds
    (c := fun _ : G.Point => N) hK (fun z hz =>
      mem_interior_iff_mem_nhds.mp (hKN hz))
  let Q := Real.sqrt (D + 4 * H * Real.sqrt H + 1)
  let modulus : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (Q * Real.sqrt |r|)
  have hcont : Continuous modulus :=
    ENNReal.continuous_ofReal.comp (continuous_const.mul
      (Real.continuous_sqrt.comp continuous_abs))
  have hzero : modulus 0 = 0 := by simp [modulus]
  have hnear : modulus ⁻¹' Iio epsilon ∈ 𝓝 (0 : ℝ) :=
    hcont.continuousAt.preimage_mem_nhds (hzero ▸ Iio_mem_nhds hepsilon)
  obtain ⟨d, hd, hmodulus⟩ := Metric.mem_nhds_iff.mp hnear
  have hsqrt : UniformContinuousOn Real.sqrt (Icc (0 : ℝ) H) :=
    isCompact_Icc.uniformContinuousOn_of_continuous Real.continuous_sqrt.continuousOn
  obtain ⟨delta, hdelta, hsqrt_delta⟩ := Metric.uniformContinuousOn_iff.mp hsqrt d hd
  refine ⟨N, hN, hKN, delta, hdelta, ?_⟩
  intro T tau x y p htau hkin henergy a ha b hb hclose hstart
  have haH : a ∈ Icc 0 H := ⟨ha.1, ha.2.trans htau⟩
  have hbH : b ∈ Icc 0 H := ⟨hb.1, hb.2.trans htau⟩
  have hroot_close : |Real.sqrt b - Real.sqrt a| < d := by
    simpa only [Real.dist_eq] using hsqrt_delta b hbH a haH
      (by simpa only [Real.dist_eq] using hclose)
  have hsmall : modulus (Real.sqrt b - Real.sqrt a) < epsilon := by
    apply hmodulus
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hroot_close
  have hbound := backward_squarePath_edist_le_sqrt p hD hkin henergy
    ⟨Real.sqrt_nonneg a, Real.sqrt_le_sqrt ha.2⟩
    ⟨Real.sqrt_nonneg b, Real.sqrt_le_sqrt hb.2⟩
  rw [Real.sq_sqrt ha.1, Real.sq_sqrt hb.1] at hbound
  have hcoeff : Real.sqrt (D + 4 * tau * Real.sqrt tau + 1) ≤ Q := by
    apply Real.sqrt_le_sqrt
    have hprod : tau * Real.sqrt tau ≤ H * Real.sqrt H :=
      mul_le_mul htau (Real.sqrt_le_sqrt htau) (Real.sqrt_nonneg tau) hH
    linarith
  have hdist : edist (p.curve a) (p.curve b) < epsilon := by
    apply (hbound.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hcoeff (Real.sqrt_nonneg _)))).trans_lt hsmall
  obtain ⟨_, hsubset⟩ := hball (p.curve a) hstart
  apply hsubset
  change edist (p.curve b) (p.curve a) < epsilon
  rwa [edist_comm]

end PoincareConjecture.Proofs.M46
