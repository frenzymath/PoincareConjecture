import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.ActualDecomposition
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.ModelCapDisks

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
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
open SaddleLevel
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1
private instance : LocallyConnectedSpace S2 := ChartedSpace.locallyConnectedSpace E2 S2

theorem closure_component_inter_compl_eq_frontier
    {X : Type*} [TopologicalSpace X] [LocallyConnectedSpace X]
    {O : Set X} (hO : IsOpen O) (p : X) :
    closure (connectedComponentIn O p) ∩ Oᶜ = frontier (connectedComponentIn O p) := by
  apply Subset.antisymm
  · rintro x ⟨hx, hn⟩
    exact ⟨hx, fun hi => hn (connectedComponentIn_subset O p (interior_subset hi))⟩
  · intro x hx
    refine ⟨hx.1, ?_⟩
    have hf := Poincare.Topology.frontier_connectedComponentIn_subset_of_isOpen hO p hx
    change x ∉ O
    simpa only [hO.interior_eq] using hf.2

theorem outside_band_component_boundary
    {h : S2 → Real} (hh : Continuous h) (a b : Real) (p : S2) :
    closure (connectedComponentIn {q | h q ∉ Icc a b} p) ∩ h ⁻¹' Icc a b =
      frontier (connectedComponentIn {q | h q ∉ Icc a b} p) := by
  have hO : IsOpen {q : S2 | h q ∉ Icc a b} :=
    (isClosed_Icc.preimage hh).isOpen_compl
  simpa only [compl_ofPred, not_not, preimage] using
    closure_component_inter_compl_eq_frontier hO p

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}

theorem terminal_modelBand_eq_image_height_band (d : TerminalSaddleGeometry M P p e) :
    d.modelBand = (fun q : S2 => d.flatten (d.filledModel q)) ''
      {q : S2 | inner Real (M.v : E3) (d.filledModel q) ∈ d.I} := by
  have hcoord (y : E3) : Saddle.toE3 (Saddle.toE2 y) (y 2) = y := by
    ext i
    fin_cases i <;> rfl
  ext y
  constructor
  · intro hy
    obtain ⟨z, hy⟩ := mem_iUnion.mp hy
    obtain ⟨hz, hy⟩ := mem_iUnion.mp hy
    change Saddle.toE3 (Saddle.toE2 y) z ∈
      d.flatten '' (d.filledModel '' sphere (0 : E3) 1) ∧ y 2 = z at hy
    obtain ⟨w, ⟨q, hq, rfl⟩, hw⟩ := hy.1
    have heq : d.flatten (d.filledModel q) = y := by
      rw [← hy.2] at hw
      exact hw.trans (hcoord y)
    refine ⟨⟨q, hq⟩, ?_, heq⟩
    change inner Real (M.v : E3) (d.filledModel q) ∈ d.I
    rw [← terminal_flatten_height d, heq, hy.2]
    exact hz
  · rintro ⟨q, hq, rfl⟩
    refine mem_iUnion_of_mem (d.flatten (d.filledModel q) 2) (mem_iUnion_of_mem ?_ ?_)
    · rwa [terminal_flatten_height]
    · change Saddle.toE3 (Saddle.toE2 (d.flatten (d.filledModel q)))
        (d.flatten (d.filledModel q) 2) ∈
        d.flatten '' (d.filledModel '' sphere (0 : E3) 1) ∧ _
      refine ⟨?_, rfl⟩
      rw [hcoord]
      exact mem_image_of_mem _ (mem_image_of_mem _ q.property)

theorem terminal_model_cap_band_boundary
    (d : TerminalSaddleGeometry M P p e) (i : Fin 3)
    (m : OpenPartialHomeomorph E2 S2) (hs : closedBall 0 1 ⊆ m.source)
    (hms : ContMDiffOn (𝓡 2) (𝓡 2) ∞ m m.source)
    (hmi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ m.symm m.target)
    (hopen : m '' ball 0 1 = connectedComponentIn
      {q : S2 | inner Real (M.v : E3) (d.filledModel q) ∉ d.I} (d.modelSeed i)) :
    d.modelCaps i ∩ d.modelBand =
      (fun x => d.flatten (d.filledModel (m x))) '' sphere (0 : E2) 1 := by
  let h : S2 → Real := fun q => inner Real (M.v : E3) (d.filledModel q)
  have hh : Continuous h := (innerSL Real (M.v : E3)).continuous.comp
    (d.filledModel.continuous.comp continuous_subtype_val)
  have hboundary : d.modelDomain i ∩ {q : S2 | h q ∈ d.I} =
      m '' sphere (0 : E2) 1 := by
    change closure (connectedComponentIn
      {q : S2 | h q ∉ Icc d.ends.lowerCut d.ends.upperCut} (d.modelSeed i)) ∩
      h ⁻¹' Icc d.ends.lowerCut d.ends.upperCut = _
    rw [outside_band_component_boundary hh]
    change frontier (connectedComponentIn
      {q : S2 | inner Real (M.v : E3) (d.filledModel q) ∉ d.I} (d.modelSeed i)) = _
    rw [← hopen, ParallelDisks.frontier_image_ball zero_lt_one m hs hms hmi]
  rw [terminal_modelBand_eq_image_height_band]
  let F : S2 → E3 := fun q => d.flatten (d.filledModel q)
  have hi : Injective F := d.flatten.injective.comp
    (d.filledModel.injective.comp Subtype.val_injective)
  change F '' d.modelDomain i ∩ F '' {q : S2 | h q ∈ d.I} = _
  rw [← image_inter hi, hboundary, image_image]

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

end

end M38Schoenflies
