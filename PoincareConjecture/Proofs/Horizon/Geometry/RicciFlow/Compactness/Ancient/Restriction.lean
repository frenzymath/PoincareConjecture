import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Ancient.Pointed
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Ancient.Window
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.GeometricLimit.Stages.SpacetimeEmbedding

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.AncientPointedGeometricConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold

def ofSubsequence {n : ℕ} {C : ℕ → FlowCarrier.{0} n}
    {g : ∀ k, ℝ → (C k).metric} {p : ∀ k, (C k).carrier} {T : ℝ}
    {σ : ℕ → ℕ} (hσ : StrictMono σ)
    (G : AncientPointedGeometricConvergence (fun k => C (σ k))
      (fun k => g (σ k)) (fun k => p (σ k)) T) :
    AncientPointedGeometricConvergence C g p T where
  limitCarrier := G.limitCarrier
  limitFlow := G.limitFlow
  base := G.base
  subsequence := σ ∘ G.subsequence
  subsequence_strictMono := hσ.comp G.subsequence_strictMono
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
  pullback_metric_converges := G.pullback_metric_converges
  pullback_metric_CInfinity := G.pullback_metric_CInfinity

noncomputable def window {n : ℕ} {C : ℕ → FlowCarrier.{0} n}
    {J : ℕ → Set ℝ} (F : ∀ k, RicciFlow n (C k).carrier (J k))
    {p : ∀ k, (C k).carrier} {T a b : ℝ}
    (G : AncientPointedGeometricConvergence C (fun k => (F k).metric) p T)
    (hab : a < b) (hb : b ≤ T) (N : ℕ)
    (hsub : ∀ k, Ioo a b ⊆ J (G.subsequence (k + N))) :
    PointedGeometricConvergence
      (sourceWindowSequence (fun k => C (G.subsequence k))
        (fun k => F (G.subsequence k)) (fun k => p (G.subsequence k)) N hsub hab) := by
  let L := G.limitCarrier
  let B := L.basedWindow G.limitFlow G.base (fun _ ht => ht.2.trans_le hb) hab
  let S := sourceWindowSequence (fun k => C (G.subsequence k))
    (fun k => F (G.subsequence k)) (fun k => p (G.subsequence k)) N hsub hab
  have hmono : Monotone G.exhaustion :=
    monotone_nat_of_le_succ G.exhaustion_increasing
  have hopen (k : ℕ) : Topology.IsOpenEmbedding
      (fun x : G.exhaustion k => G.embedding (k + N) x) :=
    (G.embedding_open (k + N)).comp (Topology.IsOpenEmbedding.inclusion
      (hmono (by omega : k ≤ k + N))
      ((G.exhaustion_open k).preimage continuous_subtype_val))
  have hsmooth (k : ℕ) : IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ∞
      (G.embedding (k + N)) (G.exhaustion k) :=
    fun x => G.embedding_smooth (k + N)
      ⟨x, hmono (by omega : k ≤ k + N) x.property⟩
  refine {
    limitCarrier := L
    limitFlow := B
    subsequence := id
    subsequence_strictMono := strictMono_id
    exhaustion := G.exhaustion
    exhaustion_open := G.exhaustion_open
    exhaustion_connected := G.exhaustion_connected
    exhaustion_compactClosure := G.exhaustion_compactClosure
    exhaustion_increasing := G.exhaustion_increasing
    exhaustion_covers := G.exhaustion_covers
    embedding := fun k => SmoothSpacetimeEmbedding.of_spatial B (S.flow k)
      (G.exhaustion_open k) (G.embedding (k + N)) (hopen k) (hsmooth k) (Ioo a b)
    base_in_exhaustion := G.base_in_exhaustion
    base_preserving := fun k => congrArg (fun x => (0, x)) (G.base_preserving (k + N))
    pullback_metric_converges := ?_
    pullback_metric_CInfinity := ?_ }
  · intro j K I hK hKE hI hIT ε hε
    obtain ⟨M, hjM, hM⟩ := G.pullback_metric_converges j K I hK hKE hI
      (fun t ht => (hIT ht).2.trans_le hb) ε hε
    refine ⟨M, hjM, fun k hk => ?_⟩
    exact hM (k + N) (by omega)
  · intro q j r K hK hKE ε hε
    obtain ⟨M, hjM, hM⟩ := G.pullback_metric_CInfinity q j r K hK
      (fun z hz => ⟨(hKE hz).1.2.trans_le hb, (hKE hz).2⟩) ε hε
    refine ⟨M, hjM, fun k hk => ?_⟩
    exact hM (k + N) (by omega)

end PoincareConjecture.AncientPointedGeometricConvergence
