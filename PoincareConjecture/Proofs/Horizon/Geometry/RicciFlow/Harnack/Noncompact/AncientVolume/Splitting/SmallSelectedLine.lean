import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Splitting.SelectedLine
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Splitting.SmallRescaledLimit















noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.RicciFlow

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold
attribute [local instance] smallCarrier smallChartedSpace smallIsManifold

set_option maxHeartbeats 600000 in




theorem exists_isometric_line_of_small_selected_terminal_segments
    {m : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
    [SecondCountableTopology M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M] [IsManifold (𝓡 (m + 1)) ∞ M]
    (hC : RicciFlowCurvatureTheory.{u}) (hm : 0 < m)
    (J : ℕ → Set ℝ) (F : ∀ i, RicciFlow (m + 1) M (J i))
    {δ Λ scale : ℝ} (hδ : 0 < δ) (hΛ : 0 ≤ Λ) (hscale : 0 < scale)
    (hpast : ∀ i a, Icc a 0 ⊆ J i)
    (hJ : ∀ i, Icc (-δ) 0 ⊆ interior (J i))
    (hcomplete : ∀ i t, t ∈ Icc (-δ) 0 → MetricComplete ((F i).metric t))
    (hRic : ∀ i t, t ∈ Icc (-δ) 0 → ∀ x : M, ∀ v : TangentSpace (𝓡 (m + 1)) x,
      0 ≤ ((F i).connection t).ricci x v v)
    (q : ℕ → M) (L : ℕ → ℝ)
    (hupper : ∀ i t, t ∈ Icc (-δ) 0 → ∀ z ∈ ((F i).metric 0).ball (q i) (L i),
      ∀ v : TangentSpace (𝓡 (m + 1)) z,
        ((F i).connection t).ricci z v v ≤ Λ * ((F i).metric t).inner z v v)
    (G : AncientPointedGeometricConvergence
      (fun _ => (FlowCarrier.ofConnectedManifold (m + 1) M).shrink)
      (fun i t => (F i).shrink.metric (t - δ)) (fun i => equivShrink M (q i)) δ)
    (hGcomplete : G.limitCarrier.metricComplete (G.limitFlow.metric 0))
    (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (hmargin : ∀ i, 4 * Real.exp (Λ * δ) * r i ≤ L (G.subsequence (σ i)))
    (minus plus : ℕ → ℝ → M) (a b : ℕ → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hminus0 : ∀ i, minus i 0 = q (G.subsequence (σ i)))
    (hplus0 : ∀ i, plus i 0 = q (G.subsequence (σ i)))
    (hminus : ∀ i, ∀ s ∈ Icc (0 : ℝ) (a i), ∀ t ∈ Icc (0 : ℝ) (a i),
      (((F (G.subsequence (σ i))).metric 0).edist (minus i s) (minus i t)).toReal = |s - t|)
    (hplus : ∀ i, ∀ s ∈ Icc (0 : ℝ) (b i), ∀ t ∈ Icc (0 : ℝ) (b i),
      (((F (G.subsequence (σ i))).metric 0).edist (plus i s) (plus i t)).toReal = |s - t|)
    (hx : ∀ i, minus i (a i) ∈
      ((F (G.subsequence (σ i))).metric 0).ball (q (G.subsequence (σ i))) (r i))
    (hy : ∀ i, plus i (b i) ∈
      ((F (G.subsequence (σ i))).metric 0).ball (q (G.subsequence (σ i))) (r i))
    (haTop : Tendsto a atTop atTop) (hbTop : Tendsto b atTop atTop)
    (hcos : Tendsto (fun i =>
      (a i ^ 2 + b i ^ 2 - (((F (G.subsequence (σ i))).metric 0).edist
        (minus i (a i)) (plus i (b i))).toReal ^ 2) / (2 * a i * b i)) atTop (𝓝 (-1)))
    (hcomparison : ∀ i (u v : ℝ → M) (A B : ℝ), 0 < A → 0 < B →
      u 0 = q (G.subsequence (σ i)) → v 0 = q (G.subsequence (σ i)) →
      (∀ s ∈ Icc (0 : ℝ) A, ∀ t ∈ Icc (0 : ℝ) A,
        (((F (G.subsequence (σ i))).metric (-δ)).edist (u s) (u t)).toReal = |s - t|) →
      (∀ s ∈ Icc (0 : ℝ) B, ∀ t ∈ Icc (0 : ℝ) B,
        (((F (G.subsequence (σ i))).metric (-δ)).edist (v s) (v t)).toReal = |s - t|) →
      ∀ s ∈ Icc (0 : ℝ) A, ∀ t ∈ Icc (0 : ℝ) B,
        s ^ 2 + t ^ 2 - 2 * s * t *
          ((A ^ 2 + B ^ 2 - (((F (G.subsequence (σ i))).metric (-δ)).edist
            (u A) (v B)).toReal ^ 2) / (2 * A * B)) ≤
          (((F (G.subsequence (σ i))).metric (-δ)).edist (u s) (v t)).toReal ^ 2) :
    letI := G.limitCarrier.metricSpaceOf (G.limitFlow.metric 0)
    ∃ gamma : ℝ → G.limitCarrier.carrier, Isometry gamma ∧ gamma 0 = G.base := by
  obtain ⟨hAB, hATop, hBTop, hangle, u, v, hend, hu, hv⟩ :=
    exists_buffered_opposite_minimizing_segments hC hm
      (fun i => J (G.subsequence (σ i))) (fun i => F (G.subsequence (σ i)))
      hδ hΛ hscale (fun i => hJ (G.subsequence (σ i)))
      (fun i => hcomplete (G.subsequence (σ i))) (fun i => hRic (G.subsequence (σ i)))
      (fun i => q (G.subsequence (σ i))) r (fun i => L (G.subsequence (σ i)))
      hr hmargin (fun i => hupper (G.subsequence (σ i)))
      minus plus a b ha hb hminus0 hplus0 hminus hplus hx hy haTop hbTop hcos
  let A := fun i => (((F (G.subsequence (σ i))).metric (-δ)).edist
    (q (G.subsequence (σ i))) (minus i (a i))).toReal
  let B := fun i => (((F (G.subsequence (σ i))).metric (-δ)).edist
    (q (G.subsequence (σ i))) (plus i (b i))).toReal
  let us : ℕ → ℝ → Shrink.{0} M := fun i t => equivShrink M (u i t)
  let vs : ℕ → ℝ → Shrink.{0} M := fun i t => equivShrink M (v i t)
  have htime : ∀ c d : ℝ, d < δ → ∀ᶠ i in atTop,
      Icc c d ⊆ (fun t : ℝ => t - δ) ⁻¹' J i := by
    intro c d hd
    exact Eventually.of_forall fun i t ht =>
      hpast i (c - δ) ⟨sub_le_sub_right ht.1 δ, by linarith [ht.2]⟩
  apply AncientPointedGeometricConvergence.exists_isometric_line_of_subsequence_opposite_segments
    (C := fun _ => (FlowCarrier.ofConnectedManifold (m + 1) M).shrink)
    (fun i => (F i).shrink.bufferedExpandingFlow δ) G hδ htime hGcomplete σ hσ us vs
    (fun i => congrArg (equivShrink M) (hend i).1)
    (fun i => congrArg (equivShrink M) (hend i).2.2.1) hATop hBTop
  · intro i s hs t ht
    change (((F (G.subsequence (σ i))).shrink.metric (0 - δ)).edist
      (equivShrink M (u i s)) (equivShrink M (u i t))).toReal = |s - t|
    rw [shrink_edist, Equiv.symm_apply_apply, Equiv.symm_apply_apply, zero_sub]
    exact hu i s hs t ht
  · intro i s hs t ht
    change (((F (G.subsequence (σ i))).shrink.metric (0 - δ)).edist
      (equivShrink M (v i s)) (equivShrink M (v i t))).toReal = |s - t|
    rw [shrink_edist, Equiv.symm_apply_apply, Equiv.symm_apply_apply, zero_sub]
    exact hv i s hs t ht
  · change Tendsto (fun i =>
      (A i ^ 2 + B i ^ 2 - (((F (G.subsequence (σ i))).shrink.metric (0 - δ)).edist
        (equivShrink M (u i (A i))) (equivShrink M (v i (B i)))).toReal ^ 2) /
          (2 * A i * B i)) atTop (𝓝 (-1))
    simp only [shrink_edist, Equiv.symm_apply_apply, zero_sub]
    simpa only [A, B, (hend _).2.1, (hend _).2.2.2] using hangle
  · intro i s hs t ht
    change s ^ 2 + t ^ 2 - 2 * s * t *
      ((A i ^ 2 + B i ^ 2 - (((F (G.subsequence (σ i))).shrink.metric (0 - δ)).edist
        (equivShrink M (u i (A i))) (equivShrink M (v i (B i)))).toReal ^ 2) /
          (2 * A i * B i)) ≤
      (((F (G.subsequence (σ i))).shrink.metric (0 - δ)).edist
        (equivShrink M (u i s)) (equivShrink M (v i t))).toReal ^ 2
    simp only [shrink_edist, Equiv.symm_apply_apply, zero_sub]
    exact hcomparison i (u i) (v i) (A i) (B i) (hAB i).1 (hAB i).2.1
      (hend i).1 (hend i).2.2.1 (hu i) (hv i) s hs t ht

end PoincareConjecture.RicciFlow
