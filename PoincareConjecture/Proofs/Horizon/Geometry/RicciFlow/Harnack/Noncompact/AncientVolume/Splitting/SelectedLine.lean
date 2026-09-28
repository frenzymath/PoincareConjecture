import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Splitting.AncientLine
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Splitting.AncientRescaledLimit
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Splitting.BufferedSegments

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.AncientPointedGeometricConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold

def alongSubsequence {n : ℕ} {C : ℕ → FlowCarrier.{0} n}
    {g : ∀ k, ℝ → (C k).metric} {p : ∀ k, (C k).carrier} {T : ℝ}
    (G : AncientPointedGeometricConvergence C g p T)
    (σ : ℕ → ℕ) (hσ : StrictMono σ) :
    AncientPointedGeometricConvergence (fun k => C (G.subsequence (σ k)))
      (fun k => g (G.subsequence (σ k))) (fun k => p (G.subsequence (σ k))) T := by
  have hmono : Monotone G.exhaustion :=
    monotone_nat_of_le_succ G.exhaustion_increasing
  refine {
    limitCarrier := G.limitCarrier
    limitFlow := G.limitFlow
    base := G.base
    subsequence := id
    subsequence_strictMono := strictMono_id
    exhaustion := G.exhaustion
    exhaustion_open := G.exhaustion_open
    exhaustion_connected := G.exhaustion_connected
    exhaustion_compactClosure := G.exhaustion_compactClosure
    exhaustion_increasing := G.exhaustion_increasing
    exhaustion_covers := G.exhaustion_covers
    embedding := fun k => G.embedding (σ k)
    embedding_open := fun k => (G.embedding_open (σ k)).comp
      (Topology.IsOpenEmbedding.inclusion (hmono (hσ.id_le k))
        ((G.exhaustion_open k).preimage continuous_subtype_val))
    embedding_smooth := fun k x =>
      G.embedding_smooth (σ k) ⟨x, hmono (hσ.id_le k) x.property⟩
    base_in_exhaustion := G.base_in_exhaustion
    base_preserving := fun k => G.base_preserving (σ k)
    pullback_metric_converges := ?_
    pullback_metric_CInfinity := ?_ }
  · intro j K I hK hKE hI hIT ε hε
    obtain ⟨N, hjN, hN⟩ := G.pullback_metric_converges j K I hK hKE hI hIT ε hε
    exact ⟨N, hjN, fun k hk => hN (σ k) (hk.trans (hσ.id_le k))⟩
  · intro q j r K hK hKE ε hε
    obtain ⟨N, hjN, hN⟩ := G.pullback_metric_CInfinity q j r K hK hKE ε hε
    exact ⟨N, hjN, fun k hk => hN (σ k) (hk.trans (hσ.id_le k))⟩

theorem exists_isometric_line_of_subsequence_source_arcs
    {n : ℕ} {C : ℕ → FlowCarrier.{0} n} {J : ℕ → Set ℝ}
    (F : ∀ k, RicciFlow n (C k).carrier (J k)) {p : ∀ k, (C k).carrier} {T : ℝ}
    (G : AncientPointedGeometricConvergence C (fun k => (F k).metric) p T)
    (hT : 0 < T)
    (htime : ∀ a b : ℝ, b < T → ∀ᶠ k in atTop, Icc a b ⊆ J k)
    (hcomplete : G.limitCarrier.metricComplete (G.limitFlow.metric 0))
    (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (arc : ∀ k, ℝ → (C (G.subsequence (σ k))).carrier)
    (hbase : ∀ k, arc k 0 = p (G.subsequence (σ k)))
    (hdist : ∀ s t : ℝ, Tendsto (fun k =>
      (((F (G.subsequence (σ k))).metric 0).edist (arc k s) (arc k t)).toReal)
        atTop (𝓝 |s - t|)) :
    letI := G.limitCarrier.metricSpaceOf (G.limitFlow.metric 0)
    ∃ gamma : ℝ → G.limitCarrier.carrier, Isometry gamma ∧ gamma 0 = G.base := by
  exact (G.alongSubsequence σ hσ).exists_isometric_line_of_source_arcs
    (fun k => F (G.subsequence (σ k))) hT
    (fun a b hb => (G.subsequence_strictMono.comp hσ).tendsto_atTop.eventually
      (htime a b hb)) hcomplete arc hbase hdist

theorem exists_isometric_line_of_subsequence_opposite_segments
    {n : ℕ} {C : ℕ → FlowCarrier.{0} n} {J : ℕ → Set ℝ}
    (F : ∀ k, RicciFlow n (C k).carrier (J k)) {p : ∀ k, (C k).carrier} {T : ℝ}
    (G : AncientPointedGeometricConvergence C (fun k => (F k).metric) p T)
    (hT : 0 < T)
    (htime : ∀ a b : ℝ, b < T → ∀ᶠ k in atTop, Icc a b ⊆ J k)
    (hcomplete : G.limitCarrier.metricComplete (G.limitFlow.metric 0))
    (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (minus plus : ∀ k, ℝ → (C (G.subsequence (σ k))).carrier)
    (hminus0 : ∀ k, minus k 0 = p (G.subsequence (σ k)))
    (hplus0 : ∀ k, plus k 0 = p (G.subsequence (σ k)))
    {a b : ℕ → ℝ} (ha : Tendsto a atTop atTop) (hb : Tendsto b atTop atTop)
    (hminus : ∀ k, ∀ s ∈ Icc (0 : ℝ) (a k), ∀ t ∈ Icc (0 : ℝ) (a k),
      (((F (G.subsequence (σ k))).metric 0).edist (minus k s) (minus k t)).toReal = |s - t|)
    (hplus : ∀ k, ∀ s ∈ Icc (0 : ℝ) (b k), ∀ t ∈ Icc (0 : ℝ) (b k),
      (((F (G.subsequence (σ k))).metric 0).edist (plus k s) (plus k t)).toReal = |s - t|)
    (hangle : Tendsto (fun k =>
      (a k ^ 2 + b k ^ 2 - (((F (G.subsequence (σ k))).metric 0).edist
        (minus k (a k)) (plus k (b k))).toReal ^ 2) / (2 * a k * b k)) atTop (𝓝 (-1)))
    (hcomparison : ∀ k, ∀ s ∈ Icc (0 : ℝ) (a k), ∀ t ∈ Icc (0 : ℝ) (b k),
      s ^ 2 + t ^ 2 - 2 * s * t *
        ((a k ^ 2 + b k ^ 2 - (((F (G.subsequence (σ k))).metric 0).edist
          (minus k (a k)) (plus k (b k))).toReal ^ 2) / (2 * a k * b k)) ≤
        (((F (G.subsequence (σ k))).metric 0).edist (minus k s) (plus k t)).toReal ^ 2) :
    letI := G.limitCarrier.metricSpaceOf (G.limitFlow.metric 0)
    ∃ gamma : ℝ → G.limitCarrier.carrier, Isometry gamma ∧ gamma 0 = G.base := by
  let : ∀ k, MetricSpace (C (G.subsequence (σ k))).carrier :=
    fun k => (C (G.subsequence (σ k))).metricSpaceOf
      ((F (G.subsequence (σ k))).metric 0)
  obtain ⟨arc, hbase, _, _, hdist⟩ :=
    Poincare.AncientVolume.Splitting.exists_two_sided_arcs_of_minimizing_segments
      (fun k => p (G.subsequence (σ k))) minus plus hminus0 hplus0
      hminus hplus ha hb hangle hcomparison
  exact G.exists_isometric_line_of_subsequence_source_arcs F hT htime hcomplete
    σ hσ arc hbase hdist

end PoincareConjecture.AncientPointedGeometricConvergence

namespace PoincareConjecture.RicciFlow

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold

set_option maxHeartbeats 600000 in

theorem exists_isometric_line_of_selected_terminal_segments
    {m : ℕ} {M : Type} [TopologicalSpace M] [T3Space M]
    [SecondCountableTopology M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M] [IsManifold (𝓡 (m + 1)) ∞ M]
    (hC : RicciFlowCurvatureTheory.{0}) (hm : 0 < m)
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
      (fun _ => FlowCarrier.ofConnectedManifold (m + 1) M)
      (fun i t => (F i).metric (t - δ)) q δ)
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
  have htime : ∀ c d : ℝ, d < δ → ∀ᶠ i in atTop,
      Icc c d ⊆ (fun t : ℝ => t - δ) ⁻¹' J i := by
    intro c d hd
    exact Eventually.of_forall fun i t ht =>
      hpast i (c - δ) ⟨sub_le_sub_right ht.1 δ, by linarith [ht.2]⟩
  apply AncientPointedGeometricConvergence.exists_isometric_line_of_subsequence_opposite_segments
    (C := fun _ => FlowCarrier.ofConnectedManifold (m + 1) M)
    (fun i => (F i).bufferedExpandingFlow δ) G hδ htime hGcomplete σ hσ u v
    (fun i => (hend i).1) (fun i => (hend i).2.2.1) hATop hBTop
  · simpa only [bufferedExpandingFlow_metric, zero_sub] using hu
  · simpa only [bufferedExpandingFlow_metric, zero_sub] using hv
  · simp only [bufferedExpandingFlow_metric, zero_sub]
    change Tendsto (fun i =>
      (A i ^ 2 + B i ^ 2 - (((F (G.subsequence (σ i))).metric (-δ)).edist
        (u i (A i)) (v i (B i))).toReal ^ 2) / (2 * A i * B i)) atTop (𝓝 (-1))
    simpa only [A, B, (hend _).2.1, (hend _).2.2.2] using hangle
  · intro i s hs t ht
    simp only [bufferedExpandingFlow_metric, zero_sub]
    exact hcomparison i (u i) (v i) (A i) (B i) (hAB i).1 (hAB i).2.1
      (hend i).1 (hend i).2.2.1 (hu i) (hv i) s hs t ht

end PoincareConjecture.RicciFlow
