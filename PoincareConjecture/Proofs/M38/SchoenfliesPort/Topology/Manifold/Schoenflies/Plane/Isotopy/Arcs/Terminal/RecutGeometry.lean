import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.TerminalData
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.OneCritical.Saddle.Resolution







open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.Poincare.Manifold.Schoenflies.PlaneArcs
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




theorem exists_terminal_geometry_with_smaller_end_cuts
    {f : S2 → E3} (M : SphereMorseReduction f)
    {g : S2 → E3} (hg : g ∈ M.tree.leaves)
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
    (d : TerminalSaddleGeometry M P p e) {ε : Real} (hε : 0 < ε) :
    ∃ d' : TerminalSaddleGeometry M P p e,
      0 < d'.eta ∧ d'.eta < ε ∧ d'.eta < d.eta ∧ d'.ends.caps.length = 3 ∧
      d'.D = d.D ∧ d'.frame = d.frame ∧ d'.r = d.r ∧ d'.delta = d.delta ∧
      d'.strips = d.strips ∧ d'.a = d.a ∧ d'.b = d.b ∧
      d'.leftContact = d.leftContact ∧ d'.rightContact = d.rightContact ∧
      d'.model = d.model ∧ d'.transport = d.transport ∧ d'.scale = d.scale ∧
      d'.modelChart = d.modelChart ∧ d'.matchingRadius = d.matchingRadius ∧
      d'.modelSeed = d.modelSeed ∧
      d'.flatten = d.flatten ∧ d'.filledModel = d.filledModel ∧
      d'.A = d.A ∧ d'.B = d.B ∧
      d'.I ⊆ Ioo (inner Real (M.v : E3) (g p) - ε)
        (inner Real (M.v : E3) (g p) + ε) ∧ d'.I ⊆ d.I := by
  classical
  obtain ⟨_, εend, _, _, _, hεend, _, _, hends⟩ :=
    M.exists_terminal_saddle_cut_resolution hg P hP hcaps hp hc
      e he0 hep he hei hform zero_lt_one
  let η := min ε (min d.eta εend) / 2
  have hmin : 0 < min ε (min d.eta εend) := lt_min hε (lt_min d.eta_pos hεend)
  have hη : 0 < η := half_pos hmin
  have hηε : η < ε := (half_lt_self hmin).trans_le (min_le_left _ _)
  have hηold : η < d.eta := (half_lt_self hmin).trans_le
    ((min_le_right ε (min d.eta εend)).trans (min_le_left _ _))
  have hηend : η ≤ εend := (half_lt_self hmin).le.trans
    ((min_le_right ε (min d.eta εend)).trans (min_le_right _ _))
  obtain ⟨ends, hlower, hupper, hcaps3, _⟩ := hends η hη hηend
  have hcard : Fintype.card ends.EndIndex = 3 := by
    rw [← Nat.card_eq_fintype_card, ends.card_endIndex_eq_caps_length, hcaps3]
  let d' : TerminalSaddleGeometry M P p e := {
    d with
    ends := ends
    eta := η
    eta_pos := hη
    eta_lt := hηold.trans d.eta_lt
    lowerCut_eq := hlower
    upperCut_eq := hupper
    labels := (Fintype.equivFinOfCardEq hcard).symm
    modelSeed_outside := by
      intro i hi
      apply d.modelSeed_outside i
      rw [hlower, hupper] at hi
      rw [d.lowerCut_eq, d.upperCut_eq]
      exact ⟨by linarith [hi.1], by linarith [hi.2]⟩ }
  refine ⟨d', hη, hηε, hηold, hcaps3, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro z hz
    change z ∈ Icc ends.lowerCut ends.upperCut at hz
    rw [hlower, hupper] at hz
    exact ⟨by linarith [hz.1], by linarith [hz.2]⟩
  · intro z hz
    change z ∈ Icc ends.lowerCut ends.upperCut at hz
    change z ∈ Icc d.ends.lowerCut d.ends.upperCut
    rw [hlower, hupper] at hz
    rw [d.lowerCut_eq, d.upperCut_eq]
    exact ⟨by linarith [hz.1], by linarith [hz.2]⟩

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

end

end M38Schoenflies
