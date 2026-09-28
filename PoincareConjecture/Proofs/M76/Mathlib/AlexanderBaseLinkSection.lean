import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseExtremeLevels
import PoincareConjecture.Proofs.M76.Mathlib.ConnectedComplexGraph
import PoincareConjecture.Proofs.M76.Mathlib.PureTriangleClosedStar
import Mathlib.Analysis.Convex.PathConnected

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]

theorem isPathConnected_space_of_connected_edgeGraph (K : SimplicialComplex ℝ E)
    (hK : K.vertexAbstractComplex.edgeGraph.Connected) : IsPathConnected K.space := by
  have hedge (u v : K.vertices) (h : K.vertexAbstractComplex.edgeGraph.Adj u v) :
      JoinedIn K.space (u : E) (v : E) := by
    have he : ({(u : E), (v : E)} : Finset E) ∈ K.faces := by
      have hface := h.2
      change ({u, v} : Finset K.vertices).map (Function.Embedding.subtype _) ∈ K.faces
        at hface
      simpa only [Finset.map_insert, Finset.map_singleton, Function.Embedding.coe_subtype]
        using hface
    apply JoinedIn.of_segment_subset
    rw [← convexHull_pair]
    simpa only [Finset.coe_insert, Finset.coe_singleton] using K.convexHull_subset_space he
  have hwalk (u v : K.vertices) (p : K.vertexAbstractComplex.edgeGraph.Walk u v) :
      JoinedIn K.space (u : E) (v : E) := by
    induction p with
    | @nil u => exact JoinedIn.refl (vertices_subset_space u.property)
    | @cons u v w h p ih => exact (hedge u v h).trans ih
  obtain ⟨u⟩ := hK.nonempty
  refine ⟨u, vertices_subset_space u.property, ?_⟩
  intro x hx
  obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
  obtain ⟨v, hvs⟩ := K.nonempty_of_mem_faces hs
  have hv : v ∈ K.vertices := K.down_closed hs
    (Finset.singleton_subset_iff.mpr hvs) (Finset.singleton_nonempty v)
  obtain ⟨p⟩ := hK u ⟨v, hv⟩
  refine (hwalk u ⟨v, hv⟩ p).trans (JoinedIn.of_segment_subset ?_)
  exact ((convex_convexHull ℝ _).segment_subset
    (subset_convexHull ℝ _ hvs) hxs).trans (K.convexHull_subset_space hs)

theorem extreme_vertex_height_link (K : SimplicialComplex ℝ E)
    (A : E →ᵃ[ℝ] ℝ) {q : E} {β : ℝ}
    (hgap : ∀ v ∈ K.vertices, v ≠ q → β < A v) :
    ∀ y ∈ (K.link q).space, β < A y := by
  intro y hy
  obtain ⟨s, hs, hys⟩ := mem_space_iff.mp hy
  apply convexHull_min (s := (s : Set E)) _ ((convex_Ioi β).affine_preimage A) hys
  intro v hv
  exact hgap v (K.down_closed hs.1 (Finset.singleton_subset_iff.mpr hv)
    (Finset.singleton_nonempty v)) (fun hvq => hs.2.1 (hvq ▸ hv))

theorem extreme_vertex_section_eq_image_link (K : SimplicialComplex ℝ E)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (A : E →ᵃ[ℝ] ℝ) {q : E} (hAq : A q = 0)
    {β : ℝ} (hβ : 0 < β) (hgap : ∀ v ∈ K.vertices, v ≠ q → β < A v) :
    K.space ∩ {x | A x = β} =
      (fun y => AffineMap.lineMap q y (β / A y)) '' (K.link q).space := by
  have hheight := K.extreme_vertex_height_link A hgap
  ext x
  constructor
  · rintro ⟨hx, hAx⟩
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
    obtain ⟨t, ht, htc, hst⟩ := hpure s hs
    have hxt := convexHull_mono hst hxs
    have hqt : q ∈ t := by
      by_contra hqt
      have hhigh : β < A x := by
        apply convexHull_min (s := (t : Set E)) _ ((convex_Ioi β).affine_preimage A) hxt
        intro v hv
        exact hgap v (K.down_closed ht (Finset.singleton_subset_iff.mpr hv)
          (Finset.singleton_nonempty v)) (fun hvq => hqt (hvq ▸ hv))
      exact (ne_of_gt hhigh) hAx
    have hcard : (t.erase q).card = 2 := by rw [Finset.card_erase_of_mem hqt, htc]
    have hne : (t.erase q).Nonempty := Finset.card_pos.mp (by omega)
    have hteq : (t : Set E) = insert q (t.erase q : Set E) := by
      rw [← Finset.coe_insert, Finset.insert_erase hqt]
    rw [hteq, convexHull_insert (show (t.erase q : Set E).Nonempty from hne)] at hxt
    obtain ⟨a, ha, y, hy, hxy⟩ := mem_convexJoin.mp hxt
    have haq : a = q := ha
    subst a
    have hylink : y ∈ (K.link q).space := mem_space_iff.mpr
      ⟨t.erase q, ⟨K.down_closed ht (Finset.erase_subset _ _) hne,
        Finset.notMem_erase _ _, by simpa only [Finset.insert_erase hqt] using ht⟩, hy⟩
    have hypos : 0 < A y := hβ.trans (hheight y hylink)
    rw [segment_eq_image_lineMap] at hxy
    obtain ⟨r, _, rfl⟩ := hxy
    have hr : r = β / A y := (eq_div_iff hypos.ne').mpr (by
      simpa only [mem_ofPred_eq, A.apply_lineMap, hAq,
        AffineMap.lineMap_apply_ring', sub_zero, add_zero]
        using hAx)
    exact ⟨y, hylink, by dsimp only; rw [← hr]⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨s, hs, hys⟩ := mem_space_iff.mp hy
    have hypos : 0 < A y := hβ.trans (hheight y hy)
    have hr : β / A y ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg hβ.le hypos.le, (div_le_one hypos).mpr (hheight y hy).le⟩
    refine ⟨K.convexHull_subset_space hs.2.2 ?_, ?_⟩
    · exact (convex_convexHull ℝ _).segment_subset
        (subset_convexHull ℝ _ (Finset.mem_insert_self q s))
        (convexHull_mono (Finset.subset_insert q s) hys)
        (lineMap_mem_segment ℝ q y hr)
    · change A (AffineMap.lineMap q y (β / A y)) = β
      rw [A.apply_lineMap, hAq, AffineMap.lineMap_apply_ring', sub_zero, add_zero,
        div_mul_cancel₀ β hypos.ne']

variable [FiniteDimensional ℝ E]

theorem isConnected_extreme_vertex_section (K : SimplicialComplex ℝ E)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (A : E →ᵃ[ℝ] ℝ) {q : E} (hAq : A q = 0)
    {β : ℝ} (hβ : 0 < β) (hgap : ∀ v ∈ K.vertices, v ≠ q → β < A v)
    (hlink : (K.link q).vertexAbstractComplex.edgeGraph.Connected) :
    IsConnected (K.space ∩ {x | A x = β}) := by
  rw [K.extreme_vertex_section_eq_image_link hpure A hAq hβ hgap]
  apply ((K.link q).isPathConnected_space_of_connected_edgeGraph hlink).isConnected.image
    (fun y => AffineMap.lineMap q y (β / A y))
  have hA := A.continuous_of_finiteDimensional.continuousOn (s := (K.link q).space)
  have hdiv : ContinuousOn (fun y => β / A y) (K.link q).space :=
    continuousOn_const.div hA (fun y hy =>
      (hβ.trans (K.extreme_vertex_height_link A hgap y hy)).ne')
  have hcont := (hdiv.smul (continuousOn_id.sub (continuousOn_const (c := q)))).add
    (continuousOn_const (c := q))
  apply hcont.congr
  intro y _
  exact AffineMap.lineMap_apply_module' q y (β / A y)

end Geometry.SimplicialComplex
