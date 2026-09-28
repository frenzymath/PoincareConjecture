import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.ModelCutGeometry

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.Poincare.Manifold.Schoenflies.PlaneArcs
open _root_.Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

open SaddleLevel

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}

def terminalModelBoundaryCircle (d : TerminalSaddleGeometry M P p e) {η : Real}
    (a : ModelCutCircleData d η) (i : Fin 3) (q : S1) : E3 :=
  d.flatten (d.filledModel (a.boundaryCircle i q))

theorem terminalModelBoundaryCircle_continuous
    (d : TerminalSaddleGeometry M P p e) {η : Real}
    (a : ModelCutCircleData d η) (i : Fin 3) :
    Continuous (terminalModelBoundaryCircle d a i) := by
  have hc : Continuous (a.boundaryCircle i) := by
    fin_cases i
    · exact (a.lower_smooth 0).continuous
    · exact (a.lower_smooth 1).continuous
    · exact a.upper_smooth.continuous
  exact d.flatten.continuous.comp
    (d.filledModel.continuous.comp (continuous_subtype_val.comp hc))

theorem terminal_model_image_height_level (d : TerminalSaddleGeometry M P p e) (z : Real) :
    (fun q : S2 => d.flatten (d.filledModel q)) ''
      {q | inner Real (M.v : E3) (d.filledModel q) = z} = Saddle.slice (d.B z) z := by
  have hcoord (y : E3) : Saddle.toE3 (Saddle.toE2 y) (y 2) = y := by
    ext i
    fin_cases i <;> rfl
  have hheight (y : E3) : d.flatten y 2 = inner Real (M.v : E3) y := by
    change d.frame (d.D y) 2 = _
    rw [d.frame_height, d.D_height]
  ext y
  constructor
  · rintro ⟨q, hq, rfl⟩
    have hh : d.flatten (d.filledModel q) 2 = z := (hheight _).trans hq
    change Saddle.toE3 (Saddle.toE2 (d.flatten (d.filledModel q))) z ∈
      d.flatten '' (d.filledModel '' sphere (0 : E3) 1) ∧ _
    refine ⟨?_, hh⟩
    rw [← hh, hcoord]
    exact mem_image_of_mem _ (mem_image_of_mem _ q.property)
  · rintro ⟨hq, hh⟩
    obtain ⟨w, ⟨q, hq, rfl⟩, heq⟩ := hq
    have heq' : d.flatten (d.filledModel q) = y := by
      rw [← hh, hcoord] at heq
      exact heq
    refine ⟨⟨q, hq⟩, ?_, heq'⟩
    change inner Real (M.v : E3) (d.filledModel q) = z
    rw [← hheight, heq', hh]

theorem iUnion_range_terminalModelBoundaryCircle
    (d : TerminalSaddleGeometry M P p e) (a : ModelCutCircleData d d.eta) :
    (⋃ i, range (terminalModelBoundaryCircle d a i)) =
      Saddle.slice (d.B d.ends.lowerCut) d.ends.lowerCut ∪
      Saddle.slice (d.B d.ends.upperCut) d.ends.upperCut := by
  have hr (i) : range (terminalModelBoundaryCircle d a i) =
      (fun q : S2 => d.flatten (d.filledModel q)) '' range (a.boundaryCircle i) := by
    change range ((fun q : S2 => d.flatten (d.filledModel q)) ∘ a.boundaryCircle i) = _
    rw [range_comp]
  have hi : (⋃ i, range (a.boundaryCircle i)) =
      {q : S2 | inner Real (M.v : E3) (d.filledModel q) = d.ends.lowerCut} ∪
      {q : S2 | inner Real (M.v : E3) (d.filledModel q) = d.ends.upperCut} := by
    rw [d.lowerCut_eq, d.upperCut_eq, a.lower_level, a.upper_level]
    ext q
    simp only [mem_iUnion, mem_union]
    constructor
    · rintro ⟨i, hi⟩
      fin_cases i
      · exact Or.inl (Or.inl hi)
      · exact Or.inl (Or.inr hi)
      · exact Or.inr hi
    · rintro ((h₀ | h₁) | h₂)
      · exact ⟨0, h₀⟩
      · exact ⟨1, h₁⟩
      · exact ⟨2, h₂⟩
  simp_rw [hr]
  rw [← image_iUnion, hi, image_union,
    terminal_model_image_height_level, terminal_model_image_height_level]

theorem range_terminalModelBoundaryCircle
    (d : TerminalSaddleGeometry M P p e) {η : Real} (a : ModelCutCircleData d η)
    (b : ModelCutDiskData d η a) (i : Fin 3) :
    range (terminalModelBoundaryCircle d a i) =
      (fun x => d.flatten (d.filledModel (b.chart i x))) '' sphere (0 : E2) 1 := by
  change range ((fun q : S2 => d.flatten (d.filledModel q)) ∘ a.boundaryCircle i) = _
  rw [range_comp, ← b.boundary i, image_image]

theorem terminalModelBoundaryCircle_pairwise_disjoint
    (d : TerminalSaddleGeometry M P p e) {η : Real} (a : ModelCutCircleData d η)
    (b : ModelCutDiskData d η a) :
    Pairwise (fun i j => Disjoint (range (terminalModelBoundaryCircle d a i))
      (range (terminalModelBoundaryCircle d a j))) := by
  have hinj : Injective (fun q : S2 => d.flatten (d.filledModel q)) :=
    d.flatten.injective.comp (d.filledModel.injective.comp Subtype.val_injective)
  intro i j hij
  have hd := (b.disjoint i j hij).mono (image_mono sphere_subset_closedBall)
    (image_mono sphere_subset_closedBall)
  rw [range_terminalModelBoundaryCircle d a b i, range_terminalModelBoundaryCircle d a b j]
  simpa only [image_image] using (Set.disjoint_image_iff hinj).mpr hd

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

end

end M38Schoenflies
