import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.ActualDecomposition
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.ActualEndDisjoint
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.BoundaryComponents

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
open SaddleLevel SphereSurgeryCoreCap
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1
private abbrev S1 := sphere (0 : E2) 1

def terminalEndCircle {v : E3} {g : S2 → E3} {B : Set Real} {C : Set S2}
    (A : AnnularEndFamily v g B C) : A.EndIndex → S1 → S2 :=
  Sum.elim A.lowerCutCircle A.upperCutCircle

theorem terminalEndCircle_range_subset {v : E3} {g : S2 → E3} {B : Set Real} {C : Set S2}
    (A : AnnularEndFamily v g B C) (i : A.EndIndex) :
    range (terminalEndCircle A i) ⊆ terminalEndCap A i := by
  rcases i with j | j
  · rintro q ⟨x, rfl⟩
    exact Or.inl (A.lowerCutCircle_mem_end j x)
  · rintro q ⟨x, rfl⟩
    exact Or.inl (A.upperCutCircle_mem_end j x)

theorem iUnion_range_terminalEndCircle
    {v : E3} {g : S2 → E3} {B : Set Real} {C : Set S2}
    (A : AnnularEndFamily v g B C) :
    (⋃ i, range (terminalEndCircle A i)) =
      {q | inner Real v (g q) = A.lowerCut} ∪
      {q | inner Real v (g q) = A.upperCut} := by
  change (⋃ i : A.LowerCutIndex ⊕ A.UpperCutIndex, range (terminalEndCircle A i)) = _
  rw [iUnion_sum]
  exact congrArg₂ (fun S T : Set S2 => S ∪ T)
    A.iUnion_range_lowerCutCircle A.iUnion_range_upperCutCircle

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}

def terminalActualBoundaryCircle (d : TerminalSaddleGeometry M P p e)
    (i : Fin 3) (q : S1) : E3 :=
  d.flatten (g (terminalEndCircle d.ends (d.labels i) q))

theorem terminalActualBoundaryCircle_continuous (d : TerminalSaddleGeometry M P p e)
    (hg : g ∈ M.tree.leaves) (i : Fin 3) :
    Continuous (terminalActualBoundaryCircle d i) := by
  have hc : Continuous (terminalEndCircle d.ends (d.labels i)) := by
    cases d.labels i with
    | inl j => exact (d.ends.lowerCutCircle_geometry j).1.continuous
    | inr j => exact (d.ends.upperCutCircle_geometry j).1.continuous
  exact d.flatten.contMDiff.continuous.comp
    ((M.tree.embedding_of_mem_leaves hg).contMDiff.continuous.comp hc)

theorem terminal_image_height_level (d : TerminalSaddleGeometry M P p e) (z : Real) :
    (d.flatten ∘ g) '' {q | inner Real (M.v : E3) (g q) = z} =
      Saddle.slice (d.A z) z := by
  have hcoord (y : E3) : Saddle.toE3 (Saddle.toE2 y) (y 2) = y := by
    ext i
    fin_cases i <;> rfl
  ext y
  constructor
  · rintro ⟨q, hq, rfl⟩
    have hh : d.flatten (g q) 2 = z := (terminal_flatten_height d _).trans hq
    change Saddle.toE3 (Saddle.toE2 (d.flatten (g q))) z ∈ d.flatten '' range g ∧ _
    refine ⟨?_, hh⟩
    rw [← hh, hcoord]
    exact mem_image_of_mem _ (mem_range_self q)
  · rintro ⟨hq, hh⟩
    obtain ⟨w, ⟨q, rfl⟩, heq⟩ := hq
    have heq' : d.flatten (g q) = y := by rw [← hh, hcoord] at heq; exact heq
    refine ⟨q, ?_, heq'⟩
    change inner Real (M.v : E3) (g q) = z
    rw [← terminal_flatten_height d, heq', hh]

theorem iUnion_range_terminalActualBoundaryCircle (d : TerminalSaddleGeometry M P p e) :
    (⋃ i, range (terminalActualBoundaryCircle d i)) =
      Saddle.slice (d.A d.ends.lowerCut) d.ends.lowerCut ∪
      Saddle.slice (d.A d.ends.upperCut) d.ends.upperCut := by
  have hr (i) : range (terminalActualBoundaryCircle d i) =
      (d.flatten ∘ g) '' range (terminalEndCircle d.ends (d.labels i)) := by
    change range ((d.flatten ∘ g) ∘ terminalEndCircle d.ends (d.labels i)) = _
    rw [range_comp]
  have hi : (⋃ i, range (terminalEndCircle d.ends (d.labels i))) =
      ⋃ j, range (terminalEndCircle d.ends j) :=
    d.labels.surjective.iUnion_comp (fun j => range (terminalEndCircle d.ends j))
  simp_rw [hr]
  rw [← image_iUnion, hi, iUnion_range_terminalEndCircle,
    image_union, terminal_image_height_level, terminal_image_height_level]

theorem range_terminalActualBoundaryCircle (d : TerminalSaddleGeometry M P p e)
    (hg : g ∈ M.tree.leaves) (i : Fin 3) :
    range (terminalActualBoundaryCircle d i) = d.C i ∩ d.actualBand := by
  rw [terminal_actualBand_eq_image_height_band]
  have hinj : Injective (d.flatten ∘ g) := d.flatten.injective.comp
    (M.tree.embedding_of_mem_leaves hg).isEmbedding.injective
  change range ((d.flatten ∘ g) ∘ terminalEndCircle d.ends (d.labels i)) =
    (d.flatten ∘ g) '' terminalEndCap d.ends (d.labels i) ∩
    (d.flatten ∘ g) '' {q | inner Real (M.v : E3) (g q) ∈ d.I}
  rw [range_comp, ← image_inter hinj, terminal_endCap_inter_height_band]
  cases d.labels i <;> rfl

theorem terminalActualBoundaryCircle_pairwise_disjoint
    (d : TerminalSaddleGeometry M P p e) :
    Pairwise (fun i j => Disjoint (range (terminalActualBoundaryCircle d i))
      (range (terminalActualBoundaryCircle d j))) := by
  have hsub (i) : range (terminalActualBoundaryCircle d i) ⊆ d.C i := by
    rintro q ⟨x, rfl⟩
    exact mem_image_of_mem _ (terminalEndCircle_range_subset d.ends _ (mem_range_self x))
  intro i j hij
  exact (terminal_actual_caps_pairwise_disjoint d hij).mono (hsub i) (hsub j)

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
