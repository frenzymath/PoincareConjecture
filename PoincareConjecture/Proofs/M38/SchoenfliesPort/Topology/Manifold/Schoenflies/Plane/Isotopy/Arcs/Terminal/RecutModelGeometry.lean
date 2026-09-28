import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.RecutGeometry
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
private abbrev S2 := sphere (0 : E3) 1

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}

def ModelCutCircleData.of_same_filledModel
    {d : TerminalSaddleGeometry M P p e} {η : Real} (a : ModelCutCircleData d η)
    (d' : TerminalSaddleGeometry M P p e) (hF : d'.filledModel = d.filledModel)
    (he : d'.modelChart = d.modelChart) : ModelCutCircleData d' η := {
  a with
  height_smooth := by simpa only [hF] using a.height_smooth
  height_center := by simpa only [hF, he] using a.height_center
  lower_level := by simpa only [hF] using a.lower_level
  separator_nonzero := by simpa only [hF] using a.separator_nonzero
  upper_level := by simpa only [hF] using a.upper_level
  lower_regular := by
    have hh : (fun q : S2 => inner Real (M.v : E3) (d'.filledModel q)) =
        (fun q : S2 => inner Real (M.v : E3) (d.filledModel q)) := by
      funext q
      rw [hF]
    intro q hq
    rw [hh]
    exact a.lower_regular q (by simpa only [hF] using hq)
  upper_regular := by
    have hh : (fun q : S2 => inner Real (M.v : E3) (d'.filledModel q)) =
        (fun q : S2 => inner Real (M.v : E3) (d.filledModel q)) := by
      funext q
      rw [hF]
    intro q hq
    rw [hh]
    exact a.upper_regular q (by simpa only [hF] using hq) }



theorem exists_terminal_geometry_with_model_cut_circles
    (M : SphereMorseReduction f) (hg : g ∈ M.tree.leaves)
    (P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g)
    (hP : P.Protects ((fun q => inner Real (M.v : E3) (M.D (f q))) ''
      {q | mfderiv (𝓡 2) 𝓘(Real, Real)
        (fun y => inner Real (M.v : E3) (M.D (f y))) q = 0}))
    (hcaps : P.PreservesCaps) {p : S2} (hp : p ∈ P.core)
    (hc : mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun q => inner Real (M.v : E3) (g q)) p = 0)
    (e : OpenPartialHomeomorph E2 S2) (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2)
    (d : TerminalSaddleGeometry M P p e) :
    ∃ d' : TerminalSaddleGeometry M P p e,
      d'.flatten = d.flatten ∧ d'.filledModel = d.filledModel ∧
      d'.scale = d.scale ∧ d'.matchingRadius = d.matchingRadius ∧
      d'.A = d.A ∧ d'.B = d.B ∧ d'.I ⊆ d.I ∧
      Nonempty (ModelCutCircleData d' d'.eta) := by
  obtain ⟨ε, hε, hcuts⟩ := exists_terminal_model_cut_circle_data d hform
  obtain ⟨d', hη, hηε, _, _, _, _, _, _, _, _, _, _, _, _, _, hscale,
    hchart, hradius, _, hflatten, hfilled, hA, hB, _, hI⟩ :=
    exists_terminal_geometry_with_smaller_end_cuts M hg P hP hcaps hp hc
      e he0 hep he hei hform d hε
  obtain ⟨a⟩ := hcuts d'.eta ⟨hη, hηε.le⟩
  exact ⟨d', hflatten, hfilled, hscale, hradius, hA, hB, hI,
    ⟨a.of_same_filledModel d' hfilled hchart⟩⟩

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

end

end M38Schoenflies
