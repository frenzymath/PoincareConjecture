import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Resolution.Hyperbola
import Mathlib.Geometry.Manifold.Diffeomorph

noncomputable section
set_option autoImplicit false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

open SaddleLevel

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1

theorem negative_morse_branch_mem_circle_of_center_mem
    (C : Fin 2 → S1 → E2) (hC : ∀ i, Continuous (C i))
    (hdis : Disjoint (range (C 0)) (range (C 1)))
    (A : Set E2) (hcover : (⋃ i, range (C i)) = A)
    (R : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    {r t : Real} (hr : 0 < r) (ht : 0 < t) (htr : t < r ^ 2)
    (hlevel : ∀ x ∈ closedSquare r, R x ∈ A ↔ -(x 0)^2 + (x 1)^2 = -t)
    (hcenter : ∀ i, R (negativeLevelArc t i 0) ∈ range (C i)) :
    ∀ i s, s ∈ Icc (-hyperbolaRadius r t) (hyperbolaRadius r t) →
      R (negativeLevelArc t i s) ∈ range (C i) := by
  intro i s hs
  let β : Real → E2 := R ∘ negativeLevelArc t i
  let I := Icc (-hyperbolaRadius r t) (hyperbolaRadius r t)
  have hβ : Continuous β := R.continuous.comp (contDiff_negativeLevelArc ht i).continuous
  have hconn : IsPreconnected (β '' I) := isPreconnected_Icc.image β hβ.continuousOn
  have hsub : β '' I ⊆ range (C 0) ∪ range (C 1) := by
    rintro x ⟨u, hu, rfl⟩
    have hx : β u ∈ A := (hlevel _ ((negativeLevelArc_mem_closedSquare hr ht htr i u).mpr hu)).mpr
      (negativeLevelArc_height ht i u)
    rw [← hcover] at hx
    simpa only [mem_iUnion, Fin.exists_fin_two, mem_union] using hx
  have hparts := isPreconnected_iff_subset_of_disjoint_closed.mp hconn
    (range (C 0)) (range (C 1)) (isCompact_range (hC 0)).isClosed
    (isCompact_range (hC 1)).isClosed hsub (by rw [hdis.inter_eq, inter_empty])
  have hzero : (0 : Real) ∈ I :=
    ⟨neg_nonpos.mpr (hyperbolaRadius_pos htr).le, (hyperbolaRadius_pos htr).le⟩
  have hmid : β 0 ∈ β '' I := mem_image_of_mem β hzero
  have hpoint : β s ∈ β '' I := mem_image_of_mem β hs
  have hc : β 0 ∈ range (C i) := hcenter i
  change β s ∈ range (C i)
  fin_cases i
  · rcases hparts with h | h
    · exact h hpoint
    · exact (disjoint_left.mp hdis hc (h hmid)).elim
  · rcases hparts with h | h
    · exact (disjoint_left.mp hdis (h hmid) hc).elim
    · exact h hpoint

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
