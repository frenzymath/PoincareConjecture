import PoincareConjecture.Proofs.M76.Mathlib.EvenGraphDecomposition
import PoincareConjecture.Proofs.M76.Mathlib.CycleSupportPolygons
import PoincareConjecture.Proofs.M76.Mathlib.GeometricGraphIntersections
import PoincareConjecture.Proofs.M76.Mathlib.DisjointCycleCover










set_option autoImplicit false

open Set

namespace SimpleGraph

variable {V E : Type*} [Finite V] [AddCommGroup E] [Module ℝ E]






theorem exists_polygons_of_exceptional_degrees_with_cycle_recognition
    (G : SimpleGraph V) (p : V → E) (q : V)
    (hdegree : ∀ v, v ≠ q → (G.neighborSet v).ncard = 2)
    (heven : Even (G.neighborSet q).ncard) (hinj : Function.Injective p)
    (hinter : ∀ ⦃v w a b⦄, G.Adj v w → G.Adj a b →
      segment ℝ (p v) (p w) ∩ segment ℝ (p a) (p b) ⊆
        convexHull ℝ (({p v, p w} : Set E) ∩ {p a, p b})) :
    ∃ (m : ℕ) (n : Fin m → ℕ) (P : ∀ i, Polygon E (n i + 3)),
      (∀ i, Function.Injective (P i) ∧ (P i).HasSimplicialEdges) ∧
      G.segmentCarrier p = ⋃ i, (P i).boundary ℝ ∧
      Pairwise (fun i j => (P i).boundary ℝ ∩ (P j).boundary ℝ ⊆ {p q}) ∧
      (Pairwise (fun i j => Disjoint ((P i).boundary ℝ) ((P j).boundary ℝ)) →
        G.IsCycles) := by
  classical
  have hall : ∀ v, Even (G.neighborSet v).ncard := by
    intro v
    by_cases hv : v = q
    · exact hv ▸ heven
    · rw [hdegree v hv]
      exact even_two
  obtain ⟨S, hS, hdisj, hcover⟩ := G.exists_cycle_graph_decomposition hall
  have hex (H : S) := (hS H.val H.property).1.exists_edgeComponent_polygons p hinj
    (fun {_ _ _ _} hvw hab => hinter ((hS H.val H.property).2.2 hvw)
      ((hS H.val H.property).2.2 hab))
  choose n P hP hunion hpair using hex
  let I := (H : S) × H.val.edgeComponents
  let nI : I → ℕ := fun i => n i.1 i.2
  let PI : ∀ i : I, Polygon E (nI i + 3) := fun i => P i.1 i.2
  have hsub (H : S) (C : H.val.edgeComponents) :
      (P H C).boundary ℝ ⊆ H.val.segmentCarrier p := by
    rw [(hP H C).2.2]
    rintro x ⟨v, w, hvw, hx⟩
    exact ⟨v.val, w.val, hvw, hx⟩
  have hcov : G.segmentCarrier p = ⋃ i : I, (PI i).boundary ℝ := by
    ext x
    constructor
    · rintro ⟨v, w, hvw, hx⟩
      obtain ⟨H, hH, hHvw⟩ := (hcover v w).mp hvw
      have hxH : x ∈ H.segmentCarrier p := ⟨v, w, hHvw, hx⟩
      rw [hunion ⟨H, hH⟩] at hxH
      obtain ⟨C, hxC⟩ := mem_iUnion.mp hxH
      exact mem_iUnion.mpr ⟨⟨⟨H, hH⟩, C⟩, hxC⟩
    · intro hx
      obtain ⟨⟨H, C⟩, hxC⟩ := mem_iUnion.mp hx
      exact segmentCarrier_mono (hS H.val H.property).2.2 p (hsub H C hxC)
  have hPI : Pairwise (fun i j : I =>
      (PI i).boundary ℝ ∩ (PI j).boundary ℝ ⊆ {p q}) := by
    rintro ⟨H, C⟩ ⟨J, D⟩ hne
    by_cases hHJ : H = J
    · subst J
      have hCD : C ≠ D := fun h => hne (by cases h; rfl)
      change (P H C).boundary ℝ ∩ (P H D).boundary ℝ ⊆ {p q}
      rw [(hpair H hCD).inter_eq]
      exact empty_subset _
    · have hd : Disjoint H.val J.val :=
        hdisj H.property J.property (fun h => hHJ (Subtype.ext h))
      have hsupp := (hS H.val H.property).1.support_inter_subset_singleton q hdegree
        (hS H.val H.property).2.2 (hS J.val J.property).2.2 hd
      exact (inter_subset_inter (hsub H C) (hsub J D)).trans
        (G.segmentCarrier_inter_subset_of_support_inter H.val J.val
          (hS H.val H.property).2.2 (hS J.val J.property).2.2 p q hinj hinter hsupp)
  let := Fintype.ofFinite I
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  refine ⟨Fintype.card I, fun i => nI (e i), fun i => PI (e i),
    fun i => ⟨(hP (e i).1 (e i).2).1, (hP (e i).1 (e i).2).2.1⟩, ?_, ?_, ?_⟩
  · rw [hcov]
    ext x
    constructor
    · intro hx
      obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
      refine mem_iUnion.mpr ⟨e.symm i, ?_⟩
      change x ∈ (PI (e (e.symm i))).boundary ℝ
      rw [e.apply_symm_apply]
      exact hxi
    · intro hx
      obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨e i, hxi⟩
  · intro i j hij
    exact hPI (fun h => hij (e.injective h))
  · intro hd
    have hIDisj : Pairwise (fun i j : I =>
        Disjoint ((PI i).boundary ℝ) ((PI j).boundary ℝ)) := by
      intro i j hij
      have h := hd (i := e.symm i) (j := e.symm j)
        (fun heq => hij (e.symm.injective heq))
      change Disjoint ((PI (e (e.symm i))).boundary ℝ)
        ((PI (e (e.symm j))).boundary ℝ) at h
      rw [e.apply_symm_apply, e.apply_symm_apply] at h
      exact h
    apply G.isCycles_of_pairwise_disjoint_segmentCarrier p (S : Set (SimpleGraph V))
      (fun H hH => (hS H hH).1) hcover
    intro H hH J hJ hHJ
    rw [hunion ⟨H, hH⟩, hunion ⟨J, hJ⟩]
    refine disjoint_iUnion_left.mpr (fun C => disjoint_iUnion_right.mpr (fun D => ?_))
    exact hIDisj (i := ⟨⟨H, hH⟩, C⟩) (j := ⟨⟨J, hJ⟩, D⟩)
      (fun heq => hHJ (congrArg (fun i : I => i.1.val) heq))





theorem exists_polygons_of_exceptional_degrees (G : SimpleGraph V) (p : V → E) (q : V)
    (hdegree : ∀ v, v ≠ q → (G.neighborSet v).ncard = 2)
    (heven : Even (G.neighborSet q).ncard) (hinj : Function.Injective p)
    (hinter : ∀ ⦃v w a b⦄, G.Adj v w → G.Adj a b →
      segment ℝ (p v) (p w) ∩ segment ℝ (p a) (p b) ⊆
        convexHull ℝ (({p v, p w} : Set E) ∩ {p a, p b})) :
    ∃ (m : ℕ) (n : Fin m → ℕ) (P : ∀ i, Polygon E (n i + 3)),
      (∀ i, Function.Injective (P i) ∧ (P i).HasSimplicialEdges) ∧
      G.segmentCarrier p = ⋃ i, (P i).boundary ℝ ∧
      Pairwise (fun i j => (P i).boundary ℝ ∩ (P j).boundary ℝ ⊆ {p q}) := by
  obtain ⟨m, n, P, hP, hcover, hpair, _⟩ :=
    G.exists_polygons_of_exceptional_degrees_with_cycle_recognition p q
      hdegree heven hinj hinter
  exact ⟨m, n, P, hP, hcover, hpair⟩

end SimpleGraph
