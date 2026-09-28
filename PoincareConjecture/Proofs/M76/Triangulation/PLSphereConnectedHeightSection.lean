import PoincareConjecture.Proofs.M76.Triangulation.PLSpherePolygonCut
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallConnected
import PoincareConjecture.Proofs.M76.Mathlib.IntrinsicRegularSection
import PoincareConjecture.Proofs.M76.Mathlib.PolygonSliceCoordinates
import Mathlib.Topology.Connected.Clopen

set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem IsFinitePL.section_eq_polygon_of_preconnected_signs
    {s : Set E} {C : Set F} {e : s ≃ₜ frontier C} (he : e.IsFinitePL)
    (hC : IsCompact C) (hcv : Convex ℝ C) (hne : (interior C).Nonempty)
    (hdim : Module.finrank ℝ F = 3) (A : E → ℝ) (c : ℝ)
    (hneg : IsPreconnected (s ∩ {x | A x < c}))
    (hpos : IsPreconnected (s ∩ {x | c < A x}))
    (hsigns : ∀ x ∈ s, A x = c →
      x ∈ closure (s ∩ {y | A y < c}) ∧
        x ∈ closure (s ∩ {y | c < A y}))
    {n : ℕ} (P : Polygon E (n + 3))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P)
    (hPs : P.boundary ℝ ⊆ s ∩ {x | A x = c}) :
    s ∩ {x | A x = c} = P.boundary ℝ := by
  have hp0 := hPs (P.vertex_mem_boundary 0)
  obtain ⟨p, hp⟩ := closure_nonempty_iff.mp
    (nonempty_of_mem (hsigns (P 0) hp0.1 hp0.2).1)
  have hpP : p ∉ P.boundary ℝ := fun h => hp.2.ne (hPs h).2
  obtain ⟨U, V, hU, hV, hcover, hinter, _⟩ :=
    he.exists_polygon_cut hC hcv hne hdim P hP hinj
      (hPs.trans inter_subset_left) ⟨p, hp.1⟩ hpP
  have hUs : U ⊆ s := subset_union_left.trans hcover.subset
  have hVs : V ⊆ s := subset_union_right.trans hcover.subset
  have hUc := hU.isCompact.isClosed
  have hVc := hV.isCompact.isClosed
  have hsplit {W : Set E} (hW : IsPreconnected W) (hWs : W ⊆ s)
      (hnz : ∀ x ∈ W, A x ≠ c) : W ⊆ U ∨ W ⊆ V := by
    apply isPreconnected_iff_subset_of_disjoint_closed.mp hW U V hUc hVc
      (hWs.trans hcover.symm.subset)
    apply eq_empty_iff_forall_notMem.mpr
    rintro x ⟨hx, hxU, hxV⟩
    exact hnz x hx (hPs (hinter.subset ⟨hxU, hxV⟩)).2
  have hnside := hsplit hneg inter_subset_left (fun x hx => (show A x < c from hx.2).ne)
  have hpside := hsplit hpos inter_subset_left (fun x hx => (show c < A x from hx.2).ne')
  have hnotU : ¬ s ⊆ U := by
    obtain ⟨x, hxV, hxP⟩ := hV.sdiff_nonempty
    exact fun h => hxP (hinter.subset ⟨h (hVs hxV), hxV⟩)
  have hnotV : ¬ s ⊆ V := by
    obtain ⟨x, hxU, hxP⟩ := hU.sdiff_nonempty
    exact fun h => hxP (hinter.subset ⟨hxU, h (hUs hxU)⟩)
  have hwhole {Z : Set E} (hZ : IsClosed Z)
      (hnZ : s ∩ {x | A x < c} ⊆ Z)
      (hpZ : s ∩ {x | c < A x} ⊆ Z) : s ⊆ Z := by
    intro x hx
    rcases lt_trichotomy (A x) c with hn | hz | hp
    · exact hnZ ⟨hx, hn⟩
    · exact closure_minimal hpZ hZ (hsigns x hx hz).2
    · exact hpZ ⟨hx, hp⟩
  apply Subset.antisymm _ hPs
  rcases hnside with hnU | hnV
  · rcases hpside with hpU | hpV
    · exact (hnotU (hwhole hUc hnU hpU)).elim
    · intro x hx
      obtain ⟨hxn, hxp⟩ := hsigns x hx.1 hx.2
      exact hinter.subset ⟨closure_minimal hnU hUc hxn, closure_minimal hpV hVc hxp⟩
  · rcases hpside with hpU | hpV
    · intro x hx
      obtain ⟨hxn, hxp⟩ := hsigns x hx.1 hx.2
      exact hinter.subset ⟨closure_minimal hpU hUc hxp, closure_minimal hnV hVc hxn⟩
    · exact (hnotV (hwhole hVc hnV hpV)).elim

theorem IsFinitePL.exists_section_polygon_of_preconnected_signs
    {s : Set E} {C : Set F} {e : s ≃ₜ frontier C} (he : e.IsFinitePL)
    (hC : IsCompact C) (hcv : Convex ℝ C) (hne : (interior C).Nonempty)
    (hdim : Module.finrank ℝ F = 3) (A : E → ℝ) (c : ℝ)
    (hneg : IsPreconnected (s ∩ {x | A x < c}))
    (hpos : IsPreconnected (s ∩ {x | c < A x}))
    (hsigns : ∀ x ∈ s, A x = c →
      x ∈ closure (s ∩ {y | A y < c}) ∧
        x ∈ closure (s ∩ {y | c < A y}))
    (hpres : HasDisjointPolygonPresentation (s ∩ {x | A x = c}))
    (hlevel : (s ∩ {x | A x = c}).Nonempty) :
    ∃ n : ℕ, ∃ P : Polygon E (n + 3),
      Function.Injective P ∧ P.HasSimplicialEdges ∧
        P.boundary ℝ = s ∩ {x | A x = c} := by
  obtain ⟨m, n, P, hP, hcover, _⟩ := hpres
  obtain ⟨x, hx⟩ := hlevel
  obtain ⟨i, _⟩ := mem_iUnion.mp (hcover.subset hx)
  have hPs : (P i).boundary ℝ ⊆ s ∩ {x | A x = c} :=
    (subset_iUnion (fun j => (P j).boundary ℝ) i).trans hcover.symm.subset
  exact ⟨n i, P i, (hP i).1, (hP i).2,
    (he.section_eq_polygon_of_preconnected_signs hC hcv hne hdim A c
      hneg hpos hsigns (P i) (hP i).2 (hP i).1 hPs).symm⟩

end Homeomorph
