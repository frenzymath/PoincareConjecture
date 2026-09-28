import PoincareConjecture.Proofs.Horizon.Topology.Surface.Euler.Incidence








set_option autoImplicit false

open Set
open scoped Manifold ContDiff

noncomputable section

open Classical

namespace PoincareConjecture.Topology.Surface

private theorem card_slots_of_two_faces {I E : Type*} [Fintype I] [Fintype E]
    (slot : I → Fin 3 → E) (hinj : ∀ i, Function.Injective (slot i))
    (adjacent : E → I × I) (hdistinct : ∀ e, (adjacent e).1 ≠ (adjacent e).2)
    (hexact : ∀ e i, (∃ k, slot i k = e) ↔
      i = (adjacent e).1 ∨ i = (adjacent e).2) :
    3 * Fintype.card I = 2 * Fintype.card E := by
  let f : I × Fin 3 → E := fun p => slot p.1 p.2
  have hcard (e : E) : Fintype.card {p : I × Fin 3 // f p = e} = 2 := by
    obtain ⟨k, hk⟩ := (hexact e (adjacent e).1).mpr (Or.inl rfl)
    obtain ⟨l, hl⟩ := (hexact e (adjacent e).2).mpr (Or.inr rfl)
    let a : {p : I × Fin 3 // f p = e} := ⟨((adjacent e).1, k), hk⟩
    let b : {p : I × Fin 3 // f p = e} := ⟨((adjacent e).2, l), hl⟩
    have hab : a ≠ b := fun h => hdistinct e (congrArg (fun p => p.1.1) h)
    have huniv : (Finset.univ : Finset {p : I × Fin 3 // f p = e}) = {a, b} := by
      ext p
      simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
      rcases (hexact e p.1.1).mp ⟨p.1.2, p.2⟩ with hp | hp
      · left
        apply Subtype.ext
        apply Prod.ext hp
        apply hinj (adjacent e).1
        have he : slot p.1.1 p.1.2 = e := p.2
        rw [hp] at he
        exact he.trans hk.symm
      · right
        apply Subtype.ext
        apply Prod.ext hp
        apply hinj (adjacent e).2
        have he : slot p.1.1 p.1.2 = e := p.2
        rw [hp] at he
        exact he.trans hl.symm
    rw [Fintype.card, huniv, Finset.card_pair hab]
  have h := Fintype.card_congr (Equiv.sigmaFiberEquiv f)
  simpa only [Fintype.card_sigma, hcard, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, Fintype.card_prod, Fintype.card_fin, Nat.mul_comm] using h.symm



theorem three_card_coordinate_faces_eq_two_card_boundary_edges
    {S : Type*} [TopologicalSpace S] [T2Space S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]
    {I : Type*} [Finite I] (face : I → SmoothFace S)
    (F : I → OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b : I → AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (hsource : ∀ i, convexHull ℝ (range (b i)) ⊆ (F i).source)
    (hcarrier : ∀ i, (face i).carrier = F i '' convexHull ℝ (range (b i)))
    (hboundary : ∀ i k, ((face i).boundary k).map = F i ∘
      affineChartSegment (b i (k.succAbove 0)) (b i (k.succAbove 1)))
    (hinj : ∀ i k, InjOn ((face i).boundary k).map (Icc (0 : ℝ) 1))
    (hinter : ∀ i j, i ≠ j →
      (∃ k l : Fin 3, (face i).carrier ∩ (face j).carrier =
          ((face i).boundary k).map '' Icc (0 : ℝ) 1 ∧
        ((face i).boundary k).map '' Icc (0 : ℝ) 1 =
          ((face j).boundary l).map '' Icc (0 : ℝ) 1) ∨
      ∃ w : Fin 3, (face i).carrier ∩ (face j).carrier ⊆ {F i (b i w)})
    (hfront : ∀ i j, i ≠ j →
      (face i).carrier ∩ (face j).carrier ⊆ frontier (face i).carrier)
    (hcover : (⋃ i, (face i).carrier) = univ) :
    3 * Nat.card I = 2 * Nat.card (FaceBoundaryEdge face) := by
  let _ := Fintype.ofFinite I
  let _ := Fintype.ofFinite (FaceBoundaryEdge face)
  obtain ⟨adjacent, hdistinct, hexact⟩ := Euler.exists_canonical_adjacentFaces
    face F b hsource hcarrier hboundary hinj hinter hfront hcover
  simpa only [Nat.card_eq_fintype_card] using card_slots_of_two_faces
    (faceBoundaryIndex face)
    (Euler.coordinate_faceBoundaryIndex_injective face F b hsource hboundary)
    adjacent hdistinct hexact

end PoincareConjecture.Topology.Surface
