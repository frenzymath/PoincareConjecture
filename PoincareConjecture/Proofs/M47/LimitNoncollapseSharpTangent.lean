import PoincareConjecture.Proofs.M47.LimitNoncollapseSharpMetric










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47



theorem limitNoncollapse_sharp_tangent_bounds
    {n m : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
    [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 m) ∞ N]
    (g : RiemannianMetric n M) (h : RiemannianMetric m N)
    {x : M} {y : N} (v : TangentSpace (𝓡 n) x) (w : TangentSpace (𝓡 m) y)
    {Q lambda : ℝ} (hQ : 0 < Q) (hlambda : 0 < lambda)
    (hlow : lambda ^ 2 * g.inner x v v ≤ Q * h.inner y w w)
    (hupp : lambda ^ 2 * (Q * h.inner y w w) ≤ g.inner x v v) :
    g.tangentNorm x v ≤ (Real.sqrt Q / lambda) * h.tangentNorm y w ∧
      h.tangentNorm y w ≤ (1 / (lambda * Real.sqrt Q)) * g.tangentNorm x v := by
  have hg : 0 ≤ g.inner x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact (g.pos x v hv).le
  have hh : 0 ≤ h.inner y w w := by
    by_cases hw : w = 0
    · simp [hw]
    · exact (h.pos y w hw).le
  constructor
  · change Real.sqrt (g.inner x v v) ≤
      (Real.sqrt Q / lambda) * Real.sqrt (h.inner y w w)
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, div_pow, Real.sq_sqrt hQ.le, Real.sq_sqrt hh]
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ (sq_pos_of_pos hlambda)).mpr (by nlinarith [hlow])
  · change Real.sqrt (h.inner y w w) ≤
      (1 / (lambda * Real.sqrt Q)) * Real.sqrt (g.inner x v v)
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, div_pow, mul_pow, Real.sq_sqrt hQ.le, Real.sq_sqrt hg, one_pow,
      div_mul_eq_mul_div, one_mul]
    exact (le_div_iff₀ (mul_pos (sq_pos_of_pos hlambda) hQ)).mpr (by
      nlinarith [hupp])

variable {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
  (G : GeneralizedBlowupConvergence S J)

private local instance : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance : ChartedSpace (EuclideanSpace ℝ (Fin 3)) G.limit.carrier.carrier :=
  G.limit.carrier.chartedSpace
private local instance : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier := G.limit.carrier.isManifold



theorem limitNoncollapse_generalized_compact_tangent_comparison
    {K : Set G.limit.sliceCarrier.carrier} (hK : IsCompact K)
    (t : ℝ) (ht : t ∈ J) {lambda : ℝ}
    (hlambda : 0 < lambda) (hlambda_lt : lambda < 1) :
    ∀ᶠ k : ℕ in atTop,
      K ⊆ G.exhaustion.space k ∧ t ∈ Icc (-G.exhaustion.time k) 0 ∧
      ∀ x ∈ K, ∀ v : TangentSpace (𝓡 3) x,
        ∀ hs : t ∈ Icc (-G.exhaustion.time k) 0,
        (G.limit.flow.metric t).tangentNorm x v ≤
          (Real.sqrt (S.scale (G.subsequence k)) / lambda) *
            ((S.flow (G.subsequence k)).metric
              ((S.base (G.subsequence k)).1 + t / S.scale (G.subsequence k))).tangentNorm
              ((G.embedding k).forward t hs x)
              (mfderiv (𝓡 3) (𝓡 3) ((G.embedding k).forward t hs) x v) ∧
        ((S.flow (G.subsequence k)).metric
            ((S.base (G.subsequence k)).1 + t / S.scale (G.subsequence k))).tangentNorm
            ((G.embedding k).forward t hs x)
            (mfderiv (𝓡 3) (𝓡 3) ((G.embedding k).forward t hs) x v) ≤
          (1 / (lambda * Real.sqrt (S.scale (G.subsequence k)))) *
            (G.limit.flow.metric t).tangentNorm x v := by
  let delta := (1 - lambda ^ 2) / 2
  have hsq : lambda ^ 2 < 1 := by nlinarith
  have hd : 0 < delta := by dsimp [delta]; linarith
  have hd1 : delta < 1 := by dsimp [delta]; nlinarith [sq_nonneg lambda]
  have hl : lambda ^ 2 ≤ 1 - delta := by dsimp [delta]; linarith
  have hu : lambda ^ 2 * (1 + delta) ≤ 1 := by
    dsimp [delta]
    nlinarith [mul_nonneg (sub_nonneg.mpr hsq.le) (sub_nonneg.mpr hsq.le)]
  filter_upwards [limitNoncollapse_generalized_compact_inner_comparison G hK t ht hd hd1]
    with k hk
  refine ⟨hk.1, hk.2.1, ?_⟩
  intro x hx v hs
  have hg : 0 ≤ (G.limit.flow.metric t).inner x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact ((G.limit.flow.metric t).pos x v hv).le
  have hb := hk.2.2 x hx v hs
  apply limitNoncollapse_sharp_tangent_bounds (G.limit.flow.metric t)
    ((S.flow (G.subsequence k)).metric
      ((S.base (G.subsequence k)).1 + t / S.scale (G.subsequence k)))
    v _ (G.embedding k).scale_pos hlambda
  · exact (mul_le_mul_of_nonneg_right hl hg).trans hb.1
  · calc
      _ ≤ lambda ^ 2 * ((1 + delta) * (G.limit.flow.metric t).inner x v v) :=
        mul_le_mul_of_nonneg_left hb.2 (sq_nonneg lambda)
      _ = (lambda ^ 2 * (1 + delta)) * (G.limit.flow.metric t).inner x v v := by ring
      _ ≤ (G.limit.flow.metric t).inner x v v := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hu hg

end PoincareConjecture.M47
