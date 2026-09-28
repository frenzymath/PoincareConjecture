import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Terminal.PairedBoundaryGeometry
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Cuts.DerivedCollarSeparation
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Cuts.DerivedCutBoundary
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Circles.BoundaryCircleAnnulus
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Circles.StandardCircleOrder










set_option autoImplicit false
open Set Metric Geometry AbstractSimplicialComplex

namespace PoincareConjecture.M76.Dehn.ProtectedAnnulus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

variable {L : Submodule ℤ V2} {α : Type*}
  {e : α → OpenPartialHomeomorph (LatticeHandleAmbient (Fin 1) (Fin 2) L) V3}
  {h : OpenPartialHomeomorph (V1 × V2) V3}
  {retained : HamiltonRetainedBlockChart (Fin 1) (Fin 2) L e h}
  {d : ProtectedAnnulusTerminalData L retained}

theorem PairedMarkedBoundary.mark_vertices (P : PairedMarkedBoundary L retained d) :
    P.mark.vertices = (P.rims false).vertices ∪ (P.rims true).vertices := by
  ext v
  change {v} ∈ P.mark.faces ↔ {v} ∈ (P.rims false).faces ∨ {v} ∈ (P.rims true).faces
  rw [P.mark_faces]
  rfl

theorem PairedMarkedBoundary.rim_full (P : PairedMarkedBoundary L retained d) (b : Bool) :
    ∀ s ∈ P.model.boundary.faces,
      (∀ v ∈ s, v ∈ (P.rims b).vertices) → s ∈ (P.rims b).faces := by
  intro s hs hv
  have hmark : s ∈ P.mark.faces := P.mark_full s (P.model.boundary_le hs) (by
    intro v hvs
    rw [P.mark_vertices]
    cases b
    · exact Or.inl (hv v hvs)
    · exact Or.inr (hv v hvs))
  rw [P.mark_faces] at hmark
  obtain ⟨v, hvs⟩ := P.model.boundary.nonempty_of_mem_faces hs
  cases b
  · rcases hmark with hm | hm
    · exact hm
    · exact (disjoint_left.mp P.disjoint
        ((P.rims false).subset_space (hv v hvs) (Finset.mem_singleton_self _))
        ((P.rims true).subset_space hm hvs)).elim
  · rcases hmark with hm | hm
    · exact (disjoint_left.mp P.disjoint ((P.rims false).subset_space hm hvs)
        ((P.rims true).subset_space (hv v hvs) (Finset.mem_singleton_self _))).elim
    · exact hm

theorem PairedMarkedBoundary.derived_collars_disjoint (P : PairedMarkedBoundary L retained d) :
    letI : Fintype P.model.boundary.faces := (P.model.finite.subset P.model.boundary_le).fintype
    Disjoint (P.model.boundary.barycentricNeighborhood (P.rims false)).space
      (P.model.boundary.barycentricNeighborhood (P.rims true)).space := by
  classical
  let : Fintype P.model.boundary.faces := (P.model.finite.subset P.model.boundary_le).fintype
  apply P.model.boundary.barycentricNeighborhood_disjoint_of_full_union
    (P.rims false) (P.rims true) ?_ P.disjoint
  intro s hs hv
  have hm := P.mark_full s (P.model.boundary_le hs)
    (fun v hvs ↦ P.mark_vertices.symm.subset (hv v hvs))
  exact P.mark_faces.subset hm



theorem PairedMarkedBoundary.exists_derived_circle_blocks
    (P : PairedMarkedBoundary L retained d) :
    letI : Fintype P.model.boundary.faces := (P.model.finite.subset P.model.boundary_le).fintype
    ∃ (n : Bool → ℕ) (p : ∀ b, Fin (n b + 3) → (P.model.sample → ℝ × V3)),
      (∀ b, Function.Injective (p b)) ∧
      (∀ b, range (p b) = (P.rims b).vertices) ∧
      (∀ b s, s ∈ (P.rims b).faces ↔ s.Nonempty ∧
        ∃ j : Fin (n b + 3), s ⊆ {p b j, p b (finRotate (n b + 3) j)}) ∧
      ∀ b, Nonempty (BoundaryCircleBlockData P.model.boundary (P.rims b) (p b)) := by
  classical
  let : Fintype P.model.boundary.faces := (P.model.finite.subset P.model.boundary_le).fintype
  have hR (b : Bool) : (P.rims b).faces.Finite :=
    P.model.finite.subset ((P.rim_le b).trans P.model.boundary_le)
  let (b : Bool) : Fintype (P.rims b).faces := (hR b).fintype
  have horders := fun b ↦ exists_original_boundary_circle_order (P.parametrization b)
    (P.parametrization_PL b) (P.rims b) (hR b) rfl
  choose n p hpi _ hpv _ hpf _ using fun b ↦ (horders b).2
  obtain ⟨hpure, hcofaces, hlinks⟩ := P.surface_incidence
  have hpure' : ∀ s ∈ P.model.boundary.faces,
      ∃ t ∈ P.model.boundary.faces, t.card = 3 ∧ s ⊆ t := by
    intro s hs
    obtain ⟨t, ht, hst, htc⟩ := hpure s hs
    exact ⟨t, ht, htc, hst⟩
  have hcofaces' (s) (hs) (hsc : s.card = 2) := hcofaces s hs hsc
  simp only [SimplicialComplex.ncard_faceLink_vertices_eq_cofaces] at hcofaces'
  obtain ⟨number, sign, hnumber, hcancel⟩ := P.exists_boundary_signs
  refine ⟨n, fun b ↦ p b, hpi, hpv, hpf, ?_⟩
  intro b
  apply exists_boundary_circle_blocks P.model.boundary (P.rims b) (P.rim_le b)
    hpure' ?_ (P.rim_full b) (horders b).1 ?_ number sign hnumber hcancel
    (p b) (hpi b) (hpv b) (hpf b)
  · intro s hs hsc
    simpa only [hsc] using hcofaces' s hs hsc
  · intro v hv
    simpa only [SimplicialComplex.faceLink_singleton_eq_link] using hlinks v (P.rim_le b hv)



theorem PairedMarkedBoundary.exists_derived_annuli (P : PairedMarkedBoundary L retained d) :
    letI : Fintype P.model.boundary.faces := (P.model.finite.subset P.model.boundary_le).fintype
    ∃ c : ∀ b : Bool, PLAnnularStrip.squareAnnulus 1 (1 / 8) ≃ₜ
        (P.model.boundary.barycentricNeighborhood (P.rims b)).space,
      (∀ b, (c b).IsFinitePL) ∧
      ∀ b x, (c b x : P.model.sample → ℝ × V3) ∈ (P.rims b).space ↔
        PLAnnularStrip.depth 1 x = 0 := by
  classical
  let : Fintype P.model.boundary.faces := (P.model.finite.subset P.model.boundary_le).fintype
  obtain ⟨n, p, hpi, hpv, hpf, hD⟩ := P.exists_derived_circle_blocks
  let D := fun b ↦ Classical.choice (hD b)
  have H := fun b ↦ BoundaryCircleBlockData.exists_annulus (P.rim_le b) (P.rim_full b)
    (hpi b) (hpv b) (hpf b) (D b)
  choose c hc _ hcore _ using H
  exact ⟨c, hc, hcore⟩

end PoincareConjecture.M76.Dehn.ProtectedAnnulus
