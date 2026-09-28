import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Orientation.Finite.TriangleSignChoice
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Orientation.Finite.AdjacentTriangles
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Orientation.Simplicial.NumberedTriangleParity
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Orientation.Simplicial.SignParity










set_option autoImplicit false

open Set Geometry PreAbstractSimplicialComplex.ModTwoCochains
open AbstractSimplicialComplex

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

variable {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]

theorem exists_frontier_all_edge_signs_of_chart_labels
    (e : ι → OpenPartialHomeomorph X V3)
    (K J : SimplicialComplex ℝ E) (hJK : J ≤ K) (hJ : J.faces.Finite)
    (g : E → X) (N : Set X)
    (hgi : InjOn g K.space) (hfront : MapsTo g J.space (frontier N))
    (hstars : ∀ p ∈ K.vertices, ∃ C : OpenPartialHomeomorph X V3,
      (∀ k, (e k).symm.trans C ∈ piecewiseAffineGroupoid V3) ∧
      MapsTo g (K.closedStar p).space C.source ∧
      (K.closedStar p).AffineOnFaces (C ∘ g) ∧
      (C.source ⊆ N ∨ ∃ (ell : V3 →ᴬ[ℝ] ℝ) (n : V3),
        ell.contLinear n = 1 ∧ ∀ y ∈ C.source, y ∈ N ↔ 0 ≤ ell (C y))) :
    let charts := {H : OpenPartialHomeomorph X V3 |
      ∀ k, (e k).symm.trans H ∈ piecewiseAffineGroupoid V3}
    let q : charts → OpenPartialHomeomorph X V3 := Subtype.val
    ∀ (hq : ∀ H D, (q H).symm.trans (q D) ∈ piecewiseAffineGroupoid V3)
      (label : ∀ H, LocallyConstant {z : J.space | g z ∈ (q H).source} PLOrientationSheet),
      (∀ H D (z : J.space) (hH : g z ∈ (q H).source) (hD : g z ∈ (q D).source),
        (label D ⟨z, hD⟩).val =
          plAtlasTransitionSign q hq H D ⟨g z, hH, hD⟩ * (label H ⟨z, hH⟩).val) →
      ∃ (number : J.vertices ↪ ℕ)
        (sigma : Triangle J.vertexAbstractComplex.toPreAbstractSimplicialComplex → ZMod 2),
        ∀ (t u : Triangle J.vertexAbstractComplex.toPreAbstractSimplicialComplex), t ≠ u →
          ∀ s : Edge J.vertexAbstractComplex.toPreAbstractSimplicialComplex,
            s.val ⊆ t.val → s.val ⊆ u.val →
            (sigma t + boundaryFaceParity number t.val s.val) +
              (sigma u + boundaryFaceParity number u.val s.val) = 1 := by
  classical
  intro charts q hq label hchange
  let := (J.finite_vertices_of_finite_faces hJ).fintype
  let V := J.vertices
  let Q := J.vertexAbstractComplex.toPreAbstractSimplicialComplex
  let number : V ↪ ℕ :=
    ⟨fun v => (Fintype.equivFin V v).val, by
      intro v w h
      exact (Fintype.equivFin V).injective (Fin.ext h)⟩
  have henumerate (t : Triangle Q) := exists_numbered_triangle_enumeration number t.val t.property.2
  choose p hpinj hpimage hpmono using henumerate
  let v : V ↪ E := Function.Embedding.subtype _
  let face (t : Triangle Q) := t.val.map v
  let point (t : Triangle Q) : Fin 3 → E := v ∘ p t
  have hface (t : Triangle Q) : face t ∈ J.faces := t.property.1
  have hpointimage (t : Triangle Q) : Finset.univ.image (point t) = face t := by
    dsimp only [point, face]
    rw [Finset.image_comp, hpimage]
    exact (Finset.map_eq_image _ _).symm
  have hpointmem (t : Triangle Q) (k : Fin 3) : point t k ∈ face t := by
    rw [← hpointimage]
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
  have hpointindep (t : Triangle Q) : AffineIndependent ℝ (point t) := by
    let f : Fin 3 ↪ face t := ⟨fun k => ⟨point t k, hpointmem t k⟩, by
      intro k l he
      exact hpinj t (v.injective (congrArg (fun z : face t => (z : E)) he))⟩
    exact (J.indep (hface t)).comp_embedding f
  let b : Module.Basis (Fin 3) ℝ V3 := Pi.basisFun ℝ (Fin 3)
  have hsign (t : Triangle Q) := exists_frontier_triangle_sign e K J hJK g N hgi hfront
    hstars b (face t) (hface t) (point t) (hpointindep t) (hpointmem t) hq label hchange
  choose sign hnonzero hcompare using hsign
  refine ⟨number, fun t => orientationSignParity (sign t), ?_⟩
  intro t u htu s hst hsu
  obtain ⟨i, hi⟩ := exists_triangle_edge_deleted_index (p t) (hpinj t) s.val t.val
    (hpimage t) hst s.property.2
  obtain ⟨j, hj⟩ := exists_triangle_edge_deleted_index (p u) (hpinj u) s.val u.val
    (hpimage u) hsu s.property.2
  have hedgeorder := numbered_triangle_common_edge_order number (p t) (p u)
    (hpmono t) (hpmono u) i j (hi.trans hj.symm)
  have hgeomi : (Finset.univ.erase i).image (point t) = s.val.map v := by
    dsimp only [point]
    rw [Finset.image_comp, hi]
    exact (Finset.map_eq_image _ _).symm
  have hgeomj : (Finset.univ.erase j).image (point u) = s.val.map v := by
    dsimp only [point]
    rw [Finset.image_comp, hj]
    exact (Finset.map_eq_image _ _).symm
  have hgeomorder : point t ∘ i.succAbove = point u ∘ j.succAbove := by
    funext k
    exact congrArg v (congrFun hedgeorder k)
  have hgeoms : s.val.map v ∈ J.faces := s.property.1
  have hfacecard (a : Triangle Q) : (face a).card = 3 := by
    dsimp only [face]
    rw [Finset.card_map]
    exact a.property.2
  have hgeomneq : face t ≠ face u := by
    intro he
    apply htu
    exact Subtype.ext (Finset.map_injective v he)
  obtain ⟨C, ell, n, A, D, hC, hCp, hCr, hA, hD, hn, hside, hdet⟩ :=
    exists_ordered_frontier_edge_chart e K J hJK g N hgi hfront hstars b
      hgeoms (hface t) (hface u) (by simpa using s.property.2)
      (hfacecard t) (hfacecard u) (Finset.map_subset_map.mpr hst)
      (Finset.map_subset_map.mpr hsu) hgeomneq (point t) (point u) (hpointindep t)
      (hpointimage t) (hpointimage u) i j hgeomi hgeomj hgeomorder
  let H : charts := ⟨C, hC⟩
  let z : convexHull ℝ (range (point t)) :=
    ⟨point t (i.succAbove 0), subset_convexHull ℝ _ (mem_range_self _)⟩
  have hw : point t (i.succAbove 0) ∈ convexHull ℝ (range (point u)) := by
    have he : point t (i.succAbove 0) = point u (j.succAbove 0) := congrFun hgeomorder 0
    rw [he]
    exact subset_convexHull ℝ _ (mem_range_self _)
  let w : convexHull ℝ (range (point u)) := ⟨point t (i.succAbove 0), hw⟩
  have htSign := hcompare t H ell n hn hCp hside A hA z
  have huSign := hcompare u H ell n hn hCr hside D hD w
  let zJ : J.space := ⟨z, J.convexHull_subset_space (hface t)
    (convexHull_mono (by rintro _ ⟨k, rfl⟩; exact hpointmem t k) z.property)⟩
  let c : PLOrientationSheet := label H ⟨zJ, hCp z.property⟩
  change sign t = c.val * SignType.sign
    (b.det ![C (g (point t 1)) - C (g (point t 0)),
      C (g (point t 2)) - C (g (point t 0)), n]) at htSign
  change sign u = c.val * SignType.sign
    (b.det ![C (g (point u 1)) - C (g (point u 0)),
      C (g (point u 2)) - C (g (point u 0)), n]) at huSign
  have hparityt := boundaryFaceParity_ordered_triangle number (p t) (hpinj t) (hpmono t) i
  have hparityu := boundaryFaceParity_ordered_triangle number (p u) (hpinj u) (hpmono u) j
  rw [hpimage t, hi] at hparityt
  rw [hpimage u, hj] at hparityu
  dsimp only
  rw [hparityt, hparityu, htSign, huSign]
  exact orientationSignParity_of_common_label _ _ c.val c.property i j hdet

end PoincareConjecture.M76
