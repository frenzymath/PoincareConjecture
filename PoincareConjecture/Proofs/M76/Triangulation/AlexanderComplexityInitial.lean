import PoincareConjecture.Proofs.M76.Triangulation.ExceptionalSlicePolygons
import PoincareConjecture.Proofs.M76.Triangulation.RegularSliceCircles
import PoincareConjecture.Proofs.M76.Mathlib.ConnectedComplexGraph
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderComplexityCharge

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_level_polygon_family_for_complexity
    (K : SimplicialComplex ℝ E) (A : E →ᵃ[ℝ] ℝ) (hK : K.faces.Finite)
    (hA : InjOn A K.vertices)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ e ∈ K.faces, e.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2)
    (c : ℝ) :
    ∃ (m : ℕ) (n : Fin m → ℕ) (P : ∀ i, Polygon E (n i + 3)) (r : Set E),
      (∀ i, Function.Injective (P i) ∧ (P i).HasSimplicialEdges) ∧
      r.Subsingleton ∧ r ⊆ K.vertices ∩ {x | A x = c} ∧
      K.space ∩ {x | A x = c} = r ∪ ⋃ i, (P i).boundary ℝ ∧
      Pairwise (fun i j => (P i).boundary ℝ ∩ (P j).boundary ℝ ⊆ r) ∧
      (c ∉ A '' K.vertices → Pairwise (fun i j =>
        Disjoint ((P i).boundary ℝ) ((P j).boundary ℝ))) := by
  classical
  let B : E →ᵃ[ℝ] ℝ := A - AffineMap.const ℝ E c
  have hB (x : E) : B x = 0 ↔ A x = c := by
    change A x - c = 0 ↔ A x = c
    exact sub_eq_zero
  by_cases hvertex : c ∈ A '' K.vertices
  · obtain ⟨q, hq, hqc⟩ := hvertex
    have hzero : ∀ v ∈ K.vertices, B v = 0 → v = q := by
      intro v hv hvB
      exact hA hv hq (((hB v).mp hvB).trans hqc.symm)
    obtain ⟨m, n, P, hP, hcover, hpair⟩ := K.exists_exceptionalSlice_polygons
      B hK hq ((hB q).mpr hqc) hzero hpure hcofaces
    refine ⟨m, n, P, {q}, hP, subsingleton_singleton,
      singleton_subset_iff.mpr ⟨hq, hqc⟩, ?_, hpair, ?_⟩
    · simpa only [hB] using hcover
    · intro hc
      exact (hc ⟨q, hq, hqc⟩).elim
  · have hreg : ∀ v ∈ K.vertices, B v ≠ 0 := by
      intro v hv hvB
      exact hvertex ⟨v, hv, (hB v).mp hvB⟩
    obtain ⟨n, P, hP, hcover, hdisj⟩ :=
      K.exists_regularSlice_polygons B hK hreg hpure hcofaces
    let C := (K.regularSliceGraph B).ConnectedComponent
    have : Finite C := K.finite_regularSliceGraph_components B hK
    let : Fintype C := Fintype.ofFinite C
    let e : Fin (Fintype.card C) ≃ C := (Fintype.equivFin C).symm
    have hdisj' : Pairwise (fun i j : Fin (Fintype.card C) =>
        Disjoint ((P (e i)).boundary ℝ) ((P (e j)).boundary ℝ)) := by
      intro i j hij
      exact hdisj (fun h => hij (e.injective h))
    refine ⟨Fintype.card C, fun i => n (e i), fun i => P (e i), ∅,
      fun i => hP (e i), subsingleton_empty, empty_subset _, ?_, ?_, fun _ => hdisj'⟩
    · rw [empty_union]
      change K.space ∩ {x | A x = c} =
        ⋃ i : Fin (Fintype.card C), (P (e i)).boundary ℝ
      rw [e.surjective.iUnion_comp (fun i => (P i).boundary ℝ)]
      simpa only [hB] using hcover
    · intro i j hij
      exact (disjoint_iff_inter_eq_empty.mp (hdisj' hij)).subset

theorem exists_finite_support_level_curve_families
    (K : SimplicialComplex ℝ E) (A : E →ᵃ[ℝ] ℝ) (hK : K.faces.Finite)
    (hA : InjOn A K.vertices)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ e ∈ K.faces, e.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2) :
    ∃ (m : ℝ → ℕ) (n : ∀ c, Fin (m c) → ℕ)
      (P : ∀ c i, Polygon E (n c i + 3)) (r : ℝ → Set E),
      (∀ c i, Function.Injective (P c i) ∧ (P c i).HasSimplicialEdges) ∧
      (∀ c, (r c).Subsingleton) ∧
      (∀ c, r c ⊆ K.vertices ∩ {x | A x = c}) ∧
      (∀ c, K.space ∩ {x | A x = c} = r c ∪ ⋃ i, (P c i).boundary ℝ) ∧
      (∀ c, Pairwise (fun i j => (P c i).boundary ℝ ∩ (P c j).boundary ℝ ⊆ r c)) ∧
      (∀ c, c ∉ A '' K.vertices →
        Pairwise (fun i j => Disjoint ((P c i).boundary ℝ) ((P c j).boundary ℝ))) ∧
      Function.support (fun c => alexanderCurveCount (fun i => (P c i).boundary ℝ)) ⊆
        A '' K.vertices ∧
      (Function.support (fun c => alexanderCurveCount (fun i => (P c i).boundary ℝ))).Finite := by
  classical
  choose m n P r hP hr hresidue hcover hpair hreg using
    K.exists_level_polygon_family_for_complexity A hK hA hpure hcofaces
  have hsupp : Function.support (fun c =>
      alexanderCurveCount (fun i => (P c i).boundary ℝ)) ⊆ A '' K.vertices := by
    intro c hc
    by_contra hcv
    exact hc (by simp only [alexanderCurveCount, if_pos (hreg c hcv)])
  exact ⟨m, n, P, r, hP, hr, hresidue, hcover, hpair, hreg, hsupp,
    ((K.finite_vertices_of_finite_faces hK).image A).subset hsupp⟩

end Geometry.SimplicialComplex
