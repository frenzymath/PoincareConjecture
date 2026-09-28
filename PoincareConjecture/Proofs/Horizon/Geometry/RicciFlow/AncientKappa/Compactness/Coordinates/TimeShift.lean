import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Coordinates.Convergence
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Normalized
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.TimeTranslation









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

namespace AncientPointedGeometricConvergence



theorem pullback_metric_CInfinity_translate
    {n : ℕ} {C : ℕ → FlowCarrier.{0} n} {g : ∀ k, ℝ → (C k).metric}
    {p : ∀ k, (C k).carrier} {T : ℝ}
    (G : AncientPointedGeometricConvergence C g p T) (c : ℝ)
    (q : G.limitCarrier.carrier) (j r : ℕ)
    (K : Set (ℝ × EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hKU : K ⊆ {z | z.1 + c < T ∧ z.2 ∈ (extChartAt (𝓡 n) q).target ∧
      (extChartAt (𝓡 n) q).symm z.2 ∈ G.exhaustion j})
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, j ≤ N ∧ ∀ k ≥ N, ∀ a b : Fin n, ∀ z ∈ K,
      ‖iteratedFDeriv ℝ r
          (G.limitCarrier.coordinateCoefficient q
            (fun t x v w => spatialPullbackInner G.limitCarrier (C (G.subsequence k))
              (g (G.subsequence k) (t + c)) (G.embedding k) x v w) a b) z -
        iteratedFDeriv ℝ r
          (G.limitCarrier.coordinateCoefficient q
            (fun t x v w => G.limitCarrier.metricInner
              (G.limitFlow.metric (t + c)) x v w) a b) z‖ < ε := by
  let d : ℝ × EuclideanSpace ℝ (Fin n) := (c, 0)
  let shift : ℝ × EuclideanSpace ℝ (Fin n) → ℝ × EuclideanSpace ℝ (Fin n) :=
    fun z => z + d
  have hshift : Continuous shift := continuous_id.add continuous_const
  have himage : shift '' K ⊆ {z | z.1 ∈ Iio T ∧
      z.2 ∈ (extChartAt (𝓡 n) q).target ∧
      (extChartAt (𝓡 n) q).symm z.2 ∈ G.exhaustion j} := by
    rintro _ ⟨z, hz, rfl⟩
    simpa only [mem_setOf_eq, shift, d, Prod.fst_add, Prod.snd_add, add_zero, mem_Iio]
      using hKU hz
  obtain ⟨N, hjN, hN⟩ := G.pullback_metric_CInfinity q j r
    (shift '' K) (hK.image hshift) himage ε hε
  refine ⟨N, hjN, fun k hk a b z hz => ?_⟩
  have hs := hN k hk a b (shift z) (mem_image_of_mem shift hz)
  let f := G.limitCarrier.coordinateCoefficient q
    (fun t x v w => spatialPullbackInner G.limitCarrier (C (G.subsequence k))
      (g (G.subsequence k) t) (G.embedding k) x v w) a b
  let l := G.limitCarrier.coordinateCoefficient q
    (fun t x v w => G.limitCarrier.metricInner (G.limitFlow.metric t) x v w) a b
  change ‖iteratedFDeriv ℝ r f (z + d) - iteratedFDeriv ℝ r l (z + d)‖ < ε at hs
  rw [← iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := f) r d z,
    ← iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := l) r d z] at hs
  have hadd (u : ℝ × EuclideanSpace ℝ (Fin n)) : u + d = (u.1 + c, u.2) :=
    Prod.ext rfl (add_zero _)
  have hf : (fun u => f (u + d)) = G.limitCarrier.coordinateCoefficient q
      (fun t x v w => spatialPullbackInner G.limitCarrier (C (G.subsequence k))
        (g (G.subsequence k) (t + c)) (G.embedding k) x v w) a b := by
    funext u
    rw [hadd]
    rfl
  have hl : (fun u => l (u + d)) = G.limitCarrier.coordinateCoefficient q
      (fun t x v w => G.limitCarrier.metricInner (G.limitFlow.metric (t + c)) x v w)
      a b := by
    funext u
    rw [hadd]
    rfl
  rwa [hf, hl] at hs



def translate
    {n : ℕ} {C : ℕ → FlowCarrier.{0} n} {g : ∀ k, ℝ → (C k).metric}
    {p : ∀ k, (C k).carrier} {T : ℝ}
    (G : AncientPointedGeometricConvergence C g p T) (c : ℝ) :
    AncientPointedGeometricConvergence C (fun k t => g k (t + c)) p (T - c) where
  limitCarrier := G.limitCarrier
  limitFlow := G.limitFlow.translate c (by
    rintro _ ⟨t, ht, rfl⟩
    exact show t + c < T by have := ht; change t < T - c at this; linarith)
    ordConnected_Iio ⟨T - c - 2, by simp, T - c - 1, by simp, by linarith⟩
  base := G.base
  subsequence := G.subsequence
  subsequence_strictMono := G.subsequence_strictMono
  exhaustion := G.exhaustion
  exhaustion_open := G.exhaustion_open
  exhaustion_connected := G.exhaustion_connected
  exhaustion_compactClosure := G.exhaustion_compactClosure
  exhaustion_increasing := G.exhaustion_increasing
  exhaustion_covers := G.exhaustion_covers
  embedding := G.embedding
  embedding_open := G.embedding_open
  embedding_smooth := G.embedding_smooth
  base_in_exhaustion := G.base_in_exhaustion
  base_preserving := G.base_preserving
  pullback_metric_converges := by
    intro j K I hK hKj hI hIt ε hε
    have hshift : (fun t : ℝ => t + c) '' I ⊆ Iio T := by
      rintro _ ⟨t, ht, rfl⟩
      have := hIt ht
      change t < T - c at this
      exact show t + c < T by linarith
    obtain ⟨N, hjN, hN⟩ := G.pullback_metric_converges j K
      ((fun t : ℝ => t + c) '' I) hK hKj
      (hI.image (continuous_id.add continuous_const)) hshift ε hε
    exact ⟨N, hjN, fun k hk t ht => hN k hk (t + c) (mem_image_of_mem _ ht)⟩
  pullback_metric_CInfinity := by
    intro q j r K hK hKU ε hε
    exact G.pullback_metric_CInfinity_translate c q j r K hK
      (fun z hz => ⟨by have := (hKU hz).1; change z.1 < T - c at this; linarith,
        (hKU hz).2⟩) ε hε

end AncientPointedGeometricConvergence

namespace NormalizedKappaSolutionSequence

local instance timeShiftSourceConnected {κ : ℝ} (S : NormalizedKappaSolutionSequence κ)
    (k : ℕ) : ConnectedSpace (S.term k).carrier.carrier := (S.term k).connectedSpace



theorem interiorLimit_pullback_metric_CInfinity_unshifted
    {κ : ℝ} (S : NormalizedKappaSolutionSequence κ)
    (G : AncientPointedGeometricConvergence (fun k => (S.term k).carrier)
      (fun k t => (S.term k).flow.flow.metric (t - 1)) (fun k => (S.term k).base) 1)
    (q : G.limitCarrier.carrier) (j r : ℕ)
    (K : Set (ℝ × EuclideanSpace ℝ (Fin 3))) (hK : IsCompact K)
    (hKU : K ⊆ {z | z.1 < 0 ∧ z.2 ∈ (extChartAt (𝓡 3) q).target ∧
      (extChartAt (𝓡 3) q).symm z.2 ∈ G.exhaustion j})
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, j ≤ N ∧ ∀ k ≥ N, ∀ a b : Fin 3, ∀ z ∈ K,
      ‖iteratedFDeriv ℝ r
          (G.limitCarrier.coordinateCoefficient q
            (fun t x v w => spatialPullbackInner G.limitCarrier
              (S.term (G.subsequence k)).carrier ((S.term (G.subsequence k)).flow.flow.metric t)
              (G.embedding k) x v w) a b) z -
        iteratedFDeriv ℝ r
          (G.limitCarrier.coordinateCoefficient q
            (fun t x v w => G.limitCarrier.metricInner
              (G.limitFlow.metric (t + 1)) x v w) a b) z‖ < ε := by
  simpa only [add_sub_cancel_right] using
    G.pullback_metric_CInfinity_translate 1 q j r K hK
      (fun z hz => ⟨by linarith [(hKU hz).1], (hKU hz).2⟩) ε hε

end NormalizedKappaSolutionSequence

end PoincareConjecture
