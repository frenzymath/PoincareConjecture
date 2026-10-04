import PoincareLib.Topology.Manifold.Smoothing.Dehn.Annuli.Surfaces.MarkedTriangleComponents
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Disks.Boundary.Circles.OrientedVertexCut

/-!
# Triangle components on the two sides of a marked circle

The actual vertex rim arcs give simple chains of original triangles.
Their internal spokes are unmarked, so each whole arc belongs to one
triangle component after cutting the marked adjacencies.
-/

set_option autoImplicit false
open Set Geometry Geometry.SimplicialComplex AbstractSimplicialComplex

namespace PoincareMT.M76.Dehn

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

/-- Actual cofaces at the ends of one vertex rim arc lie in the same
component after deleting the marked-edge adjacencies. -/
theorem vertex_rim_arc_cofaces_same_marked_component
    (A L : SimplicialComplex ℝ E) [Fintype A.faces]
    (v : E) (p : Bool → E) (hvp : ∀ j, v ≠ p j) (hpne : p false ≠ p true)
    (hedge : ∀ j, {v, p j} ∈ A.faces)
    (hmarked : ∀ s ∈ L.faces, v ∈ s → s.card = 2 →
      s = {v, p false} ∨ s = {v, p true})
    (arc : Bool → Set E) (hclosed : ∀ b, IsClosed (arc b))
    (hconnected : ∀ b, IsPreconnected (arc b))
    (hcover : arc false ∪ arc true = (A.barycentricSubdivision.link v).space)
    (hinter : arc false ∩ arc true =
      {({v, p false} : Finset E).centroid ℝ id, ({v, p true} : Finset E).centroid ℝ id})
    (hend : ∀ j b, ({v, p j} : Finset E).centroid ℝ id ∈ arc b)
    (t : Bool → Bool → Finset E)
    (hexhaust : ∀ j u, u ∈ A.faces → u.card = 3 → {v, p j} ⊆ u →
      u = t j false ∨ u = t j true)
    (htarc : ∀ j b, (t j b).centroid ℝ id ∈ arc b)
    (C : (A.markedTriangleGraph L).ConnectedComponent) (b : Bool) :
    t false b ∈ (A.markedTriangleComponent L C).faces ↔
      t true b ∈ (A.markedTriangleComponent L C).faces := by
  classical
  have hnot (u : Finset E) (hu : u ∈ A.faces) (huc : u.card = 3) :
      u.centroid ℝ id ∉
        ({({v, p false} : Finset E).centroid ℝ id,
          ({v, p true} : Finset E).centroid ℝ id} : Set E) := by
    rintro (h | h)
    all_goals
      have he := congrArg Subtype.val (A.faceCentroid_injective
        (a₁ := ⟨u, hu⟩) (a₂ := ⟨_, hedge _⟩) h)
      have hc := congrArg Finset.card he
      simp only [huc, Finset.card_pair (hvp _)] at hc
      omega
  have hunique (j b : Bool) (u : Finset E) (hu : u ∈ A.faces)
      (huc : u.card = 3) (hsu : {v, p j} ⊆ u) (hU : u.centroid ℝ id ∈ arc b) :
      u = t j b := by
    rcases hexhaust j u hu huc hsu with h | h
    · cases b
      · exact h
      · exact False.elim (hnot u hu huc (hinter ▸ ⟨h.symm ▸ htarc j false, hU⟩))
    · cases b
      · exact False.elim (hnot u hu huc (hinter ▸ ⟨hU, h.symm ▸ htarc j true⟩))
      · exact h
  have hcover' : arc b ∪ arc (!b) = (A.barycentricSubdivision.link v).space := by
    cases b
    · exact hcover
    · simpa only [Bool.not_true, union_comm] using hcover
  have hinter' : arc b ∩ arc (!b) ⊆
      {({v, p false} : Finset E).centroid ℝ id,
        ({v, p true} : Finset E).centroid ℝ id} := by
    cases b
    · exact hinter.subset
    · simpa only [Bool.not_true, inter_comm] using hinter.subset
  obtain ⟨n, q, hn, hq0, hqn, hqi, hvq, hqtri⟩ :=
    exists_original_triangle_chain_in_vertex_rim_arc A (hvp false) (hvp true) hpne
      (hedge false) (hedge true) (arc b) (arc (!b)) (hclosed b) (hclosed (!b))
      hcover' hinter' (hconnected b) (hend false b) (hend true b)
  let tri : ℕ → Finset E := fun k ↦ {v, q k, q (k + 1)}
  have hfirst : tri 0 = t false b := by
    apply hunique false b _ (hqtri 0 hn).2.1 (hqtri 0 hn).2.2.1
    · simp [hq0]
    · exact (hqtri 0 hn).2.2.2
  have hlast : tri (n - 1) = t true b := by
    have hlast : n - 1 < n := by omega
    apply hunique true b _ (hqtri _ hlast).2.1 (hqtri _ hlast).2.2.1
    · simp [Nat.sub_add_cancel hn, hqn]
    · exact (hqtri _ hlast).2.2.2
  have hstep (k : ℕ) (hk : k + 1 < n) :
      tri k ∈ (A.markedTriangleComponent L C).faces ↔
        tri (k + 1) ∈ (A.markedTriangleComponent L C).faces := by
    let s : Finset E := {v, q (k + 1)}
    have hsc : s.card = 2 := Finset.card_pair (hvq _ hk.le)
    have hmark : s ∉ L.faces := by
      intro hs
      rcases hmarked s hs (by simp [s]) hsc with he | he
      all_goals
        have hmem : q (k + 1) ∈ s := by simp [s]
        rw [he] at hmem
        rcases Finset.mem_insert.mp hmem with hv | hp
        · exact hvq _ hk.le hv.symm
        · have hp := Finset.mem_singleton.mp hp
          first
          | have hi := hqi ⟨Nat.zero_le _, hk.le⟩ ⟨Nat.zero_le _, hn.le⟩
              (hp.trans hq0.symm)
            omega
          | have hi := hqi ⟨Nat.zero_le _, hk.le⟩ ⟨Nat.zero_le _, le_rfl⟩
              (hp.trans hqn.symm)
            omega
    have hs0 : s ⊆ tri k := by simp [s, tri]
    have hs1 : s ⊆ tri (k + 1) := by simp [s, tri]
    constructor
    · intro h
      exact A.markedTriangleComponent_unmarked_coface L C
        ((A.markedTriangleComponent L C).down_closed h hs0 (by simp [s])) hsc hmark
        (hqtri _ hk).2.1 (hqtri _ hk).2.2.1 hs1
    · intro h
      exact A.markedTriangleComponent_unmarked_coface L C
        ((A.markedTriangleComponent L C).down_closed h hs1 (by simp [s])) hsc hmark
        (hqtri k (by omega)).2.1 (hqtri k (by omega)).2.2.1 hs0
  have hall (k : ℕ) (hk : k < n) :
      tri 0 ∈ (A.markedTriangleComponent L C).faces ↔
        tri k ∈ (A.markedTriangleComponent L C).faces := by
    induction k with
    | zero => rfl
    | succ k ih => exact (ih (by omega)).trans (hstep k hk)
  simpa only [hfirst, hlast] using hall (n - 1) (by omega)

/-- Coherent orientation selects the same component at both incident
marked edges. The required rim arcs are constructed from the actual surface. -/
theorem oriented_vertex_cofaces_same_marked_component
    (A L : SimplicialComplex ℝ E) [Fintype A.faces] [Fintype L.faces]
    (hLA : L ≤ A)
    (hpure : ∀ s ∈ A.faces, ∃ t ∈ A.faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ s ∈ A.faces, s.card = 2 →
      {t : Finset E | t ∈ A.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (hfull : ∀ t ∈ A.faces, (∀ v ∈ t, v ∈ L.vertices) → t ∈ L.faces)
    (hLcard : ∀ s ∈ L.faces, s.card ≤ 2)
    (number : E → ℕ) (sign : Finset E → ZMod 2) (hnumber : InjOn number A.vertices)
    (hcancel : ∀ t ∈ A.faces, t.card = 3 → ∀ u ∈ A.faces, u.card = 3 → t ≠ u →
      ∀ s : Finset E, s.card = 2 → s ⊆ t → s ⊆ u →
        (sign t + boundaryFaceParity number t s) +
          (sign u + boundaryFaceParity number u s) = 1)
    (v : E) (p : Bool → E) (hvp : ∀ j, v ≠ p j) (hpne : p false ≠ p true)
    (hedge : ∀ j, ({v, p j} : Finset E) ∈ L.faces)
    (hlink : IsConnected (A.link v).space)
    (hexhaust : ∀ s ∈ L.faces, v ∈ s → s.card = 2 →
      s = {v, p false} ∨ s = {v, p true})
    (t : Bool → Bool → Finset E)
    (ht : ∀ j b, t j b ∈ A.faces ∧ (t j b).card = 3 ∧ ({v, p j} : Finset E) ⊆ t j b)
    (htex : ∀ j u, u ∈ A.faces → u.card = 3 → ({v, p j} : Finset E) ⊆ u →
      u = t j false ∨ u = t j true)
    (htsign : ∀ j b, sign (t j b) + orderedCofaceParity number (t j b)
      (if j then v else p false) (if j then p true else v) = if b then 1 else 0)
    (C : (A.markedTriangleGraph L).ConnectedComponent) (b : Bool) :
    t false b ∈ (A.markedTriangleComponent L C).faces ↔
      t true b ∈ (A.markedTriangleComponent L C).faces := by
  obtain ⟨_, _, U, _, hU, _, _, hcover, hinter, _, _, hsegments⟩ :=
    exists_oriented_boundary_vertex_cut A L hLA hpure hcofaces hfull hLcard
      number sign hnumber hcancel v p hvp hpne hedge hlink hexhaust t ht htex htsign
  exact vertex_rim_arc_cofaces_same_marked_component A L v p hvp hpne
    (fun j ↦ hLA (hedge j)) hexhaust U (fun b ↦ (hU b).isCompact.isClosed)
    (fun b ↦ (hU b).isConnected.isPreconnected) hcover hinter
    (fun j b ↦ hsegments j b (left_mem_segment ℝ _ _)) t htex
    (fun j b ↦ hsegments j b (right_mem_segment ℝ _ _)) C b

end PoincareMT.M76.Dehn
