import PoincareConjecture.Proofs.M76.PrimeReduction.ActualGraphCarrier
import PoincareConjecture.Proofs.M76.Mathlib.PolygonPathCycles









set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]





theorem exists_actual_component_interval
    (J : SimplicialComplex ℝ E) (hJ : J.faces.Finite)
    (hdegree : ∀ v, (J.vertexAbstractComplex.edgeGraph.neighborSet v).ncard ≤ 2)
    (C : J.vertexAbstractComplex.edgeGraph.ConnectedComponent)
    (hleaf : ∃ v : C, (J.vertexAbstractComplex.edgeGraph.neighborSet v.val).ncard = 1) :
    ∃ (n : ℕ) (e : Fin (n + 2) ≃ C),
      C.toSimpleGraph.segmentCarrier (fun v => (v.val : E)) =
        Polygon.pathCarrier (fun i => ((e i).val : E)) ∧
      IsFinitePLBallPair ℝ (C.toSimpleGraph.segmentCarrier (fun v => (v.val : E)))
        {((e 0).val : E), ((e (Fin.last (n + 1))).val : E)} ∧
      (Subtype.val '' {v : J.vertices | v ∈ C.supp ∧
        (J.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1}) =
        {((e 0).val : E), ((e (Fin.last (n + 1))).val : E)} ∧
      ∀ v w : C, C.toSimpleGraph.Adj v w ↔ ∃ i : Fin (n + 1),
        (e i.castSucc = v ∧ e i.succ = w) ∨
        (e i.castSucc = w ∧ e i.succ = v) := by
  classical
  let : Finite J.vertices := (J.finite_vertices_of_finite_faces hJ).to_subtype
  let G := J.vertexAbstractComplex.edgeGraph
  obtain ⟨a, ha⟩ := hleaf
  obtain ⟨n, e, _, he, hends⟩ :=
    C.toSimpleGraph.exists_linear_labels_from_leaf_with_endpoints C.connected_toSimpleGraph
      (fun v => (C.ncard_neighborSet G v).le.trans (hdegree v.val))
      ((C.ncard_neighborSet G a).trans ha)
  let p : C → E := fun v => (v.val : E)
  have hpi : Function.Injective p := Subtype.val_injective.comp Subtype.val_injective
  have hadj (i : Fin (n + 1)) : C.toSimpleGraph.Adj (e i.castSucc) (e i.succ) :=
    (he _ _).mpr ⟨i, Or.inl ⟨rfl, rfl⟩⟩
  have hinter (i j : Fin (n + 1)) :
      segment ℝ (p (e i.castSucc)) (p (e i.succ)) ∩
          segment ℝ (p (e j.castSucc)) (p (e j.succ)) ⊆
        convexHull ℝ (({p (e i.castSucc), p (e i.succ)} : Set E) ∩
          {p (e j.castSucc), p (e j.succ)}) :=
    J.actual_edgeGraph_segment_intersection (hadj i) (hadj j)
  have hcarrier := C.toSimpleGraph.segmentCarrier_eq_linear_chain p e he
  have hball := Set.isFinitePLBallPair_linear_chain (p ∘ e) (hpi.comp e.injective) hinter
  have hball' : IsFinitePLBallPair ℝ (C.toSimpleGraph.segmentCarrier p)
      {p (e 0), p (e (Fin.last (n + 1)))} := by
    rw [hcarrier]
    exact hball
  refine ⟨n, e, hcarrier, hball', ?_, he⟩
  ext x
  constructor
  · rintro ⟨v, ⟨hvC, hv⟩, rfl⟩
    have h := (hends ⟨v, hvC⟩).mp ((C.ncard_neighborSet G ⟨v, hvC⟩).trans hv)
    rcases h with h | h
    · exact Or.inl (congrArg (fun z : C => (z.val : E)) h)
    · exact Or.inr (congrArg (fun z : C => (z.val : E)) h)
  · rintro (hx | hx)
    · refine ⟨(e 0).val, ⟨(e 0).property, ?_⟩, hx.symm⟩
      exact (C.ncard_neighborSet G (e 0)).symm.trans
        ((hends (e 0)).mpr (Or.inl rfl))
    · refine ⟨(e (Fin.last (n + 1))).val, ⟨(e (Fin.last (n + 1))).property, ?_⟩, hx.symm⟩
      exact (C.ncard_neighborSet G (e (Fin.last (n + 1)))).symm.trans
        ((hends (e (Fin.last (n + 1)))).mpr (Or.inr rfl))

end Geometry.SimplicialComplex
