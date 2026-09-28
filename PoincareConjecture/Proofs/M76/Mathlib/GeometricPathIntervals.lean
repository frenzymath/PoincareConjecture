import PoincareConjecture.Proofs.M76.Mathlib.FinitePathLabels
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLLinearChain
import PoincareConjecture.Proofs.M76.Mathlib.GeometricGraphComponents










set_option autoImplicit false

open Set

namespace SimpleGraph

variable {V E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]




theorem segmentCarrier_eq_linear_chain (G : SimpleGraph V) (p : V → E)
    {n : ℕ} (e : Fin (n + 2) ≃ V)
    (he : ∀ v w, G.Adj v w ↔ ∃ i : Fin (n + 1),
      (e i.castSucc = v ∧ e i.succ = w) ∨ (e i.castSucc = w ∧ e i.succ = v)) :
    G.segmentCarrier p = ⋃ i : Fin (n + 1), segment ℝ (p (e i.castSucc)) (p (e i.succ)) := by
  ext x
  constructor
  · rintro ⟨v, w, hvw, hx⟩
    obtain ⟨i, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := (he v w).mp hvw
    · exact mem_iUnion.mpr ⟨i, hx⟩
    · exact mem_iUnion.mpr ⟨i, by simpa only [segment_symm] using hx⟩
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact ⟨e i.castSucc, e i.succ, (he _ _).mpr ⟨i, Or.inl ⟨rfl, rfl⟩⟩, hi⟩

variable [Finite V] [FiniteDimensional ℝ E]





theorem isFinitePLBallPair_segmentCarrier_of_leaf (G : SimpleGraph V) (p : V → E)
    (hconn : G.Connected) (hdegree : ∀ v, (G.neighborSet v).ncard ≤ 2)
    (hleaf : ∃ v, (G.neighborSet v).ncard = 1) (hp : Function.Injective p)
    (hinter : ∀ ⦃v w a b⦄, G.Adj v w → G.Adj a b →
      segment ℝ (p v) (p w) ∩ segment ℝ (p a) (p b) ⊆
        convexHull ℝ (({p v, p w} : Set E) ∩ {p a, p b})) :
    IsFinitePLBallPair ℝ (G.segmentCarrier p) (p '' {v | (G.neighborSet v).ncard = 1}) := by
  obtain ⟨a, ha⟩ := hleaf
  obtain ⟨n, e, _, he, hends⟩ :=
    G.exists_linear_labels_from_leaf_with_endpoints hconn hdegree ha
  have hadj (i : Fin (n + 1)) : G.Adj (e i.castSucc) (e i.succ) :=
    (he _ _).mpr ⟨i, Or.inl ⟨rfl, rfl⟩⟩
  have hball := isFinitePLBallPair_linear_chain (fun i => p (e i))
    (hp.comp e.injective) (fun i j => hinter (hadj i) (hadj j))
  have hset : {v | (G.neighborSet v).ncard = 1} = {e 0, e (Fin.last (n + 1))} :=
    Set.ext (fun v => hends v)
  rw [hset, image_pair, G.segmentCarrier_eq_linear_chain p e he]
  exact hball






theorem finitePL_interval_components (G : SimpleGraph V) (p : V → E)
    (hdegree : ∀ v, (G.neighborSet v).ncard ≤ 2)
    (hleaf : ∀ C : G.ConnectedComponent, ∃ v : C, (G.neighborSet v.val).ncard = 1)
    (hp : Function.Injective p)
    (hinter : ∀ ⦃v w a b⦄, G.Adj v w → G.Adj a b →
      segment ℝ (p v) (p w) ∩ segment ℝ (p a) (p b) ⊆
        convexHull ℝ (({p v, p w} : Set E) ∩ {p a, p b})) :
    (∀ C : G.ConnectedComponent,
      IsFinitePLBallPair ℝ (C.toSimpleGraph.segmentCarrier (fun v => p v.val))
        (p '' {v | v ∈ C.supp ∧ (G.neighborSet v).ncard = 1})) ∧
    G.segmentCarrier p = ⋃ C : G.ConnectedComponent,
      C.toSimpleGraph.segmentCarrier (fun v => p v.val) ∧
    Pairwise (fun C D : G.ConnectedComponent =>
      Disjoint (C.toSimpleGraph.segmentCarrier (fun v => p v.val))
        (D.toSimpleGraph.segmentCarrier (fun v => p v.val))) := by
  refine ⟨?_, G.segmentCarrier_eq_iUnion_components p,
    G.pairwise_disjoint_component_segmentCarrier p hp hinter⟩
  intro C
  have hball := C.toSimpleGraph.isFinitePLBallPair_segmentCarrier_of_leaf
    (fun v => p v.val) C.connected_toSimpleGraph
    (fun v => (C.ncard_neighborSet G v).le.trans (hdegree v.val))
    (by
      obtain ⟨v, hv⟩ := hleaf C
      exact ⟨v, (C.ncard_neighborSet G v).trans hv⟩)
    (hp.comp Subtype.val_injective) (fun {_ _ _ _} h h' => hinter h h')
  have hboundary : (fun v : C => p v.val) ''
      {v : C | (C.toSimpleGraph.neighborSet v).ncard = 1} =
        p '' {v | v ∈ C.supp ∧ (G.neighborSet v).ncard = 1} := by
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v.val, ⟨v.property, (C.ncard_neighborSet G v).symm.trans hv⟩, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨⟨v, hv.1⟩, (C.ncard_neighborSet G ⟨v, hv.1⟩).trans hv.2, rfl⟩
  rwa [hboundary] at hball

end SimpleGraph
