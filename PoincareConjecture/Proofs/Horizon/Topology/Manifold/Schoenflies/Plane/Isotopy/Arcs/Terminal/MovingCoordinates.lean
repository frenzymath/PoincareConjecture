import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.HeightFibers
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.NestedGeometry



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

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}

private theorem fiber_mem_image_iff
    (d : TerminalSaddleGeometry M P p e) (z : Real) (x : E2) (S : Set E3) :
    Saddle.toE3 (terminalHeightFiber d z x) z ∈ d.flatten '' S ↔
      Saddle.toE3 x z ∈ d.frame '' S := by
  rw [terminalHeightFiber_lift]
  constructor
  · rintro ⟨q, hqS, hq⟩
    have hh : q = d.frame.symm (Saddle.toE3 x z) := d.D.injective (d.frame.injective hq)
    refine ⟨q, hqS, ?_⟩
    rw [hh, d.frame.apply_symm_apply]
  · rintro ⟨q, hqS, hq⟩
    refine ⟨q, hqS, ?_⟩
    change d.frame (d.D q) = d.frame (d.D (d.frame.symm (Saddle.toE3 x z)))
    rw [← hq, d.frame.symm_apply_apply]


theorem terminalHeightFiber_mem_actual_slice_iff
    (d : TerminalSaddleGeometry M P p e) (z : Real) (x : E2) :
    terminalHeightFiber d z x ∈ d.A z ↔ Saddle.toE3 x z ∈ d.frame '' range g :=
  fiber_mem_image_iff d z x _


theorem terminalHeightFiber_mem_model_slice_iff
    (d : TerminalSaddleGeometry M P p e) (z : Real) (x : E2) :
    terminalHeightFiber d z x ∈ d.B z ↔
      Saddle.toE3 x z ∈ d.frame '' (d.filledModel '' sphere (0 : E3) 1) :=
  fiber_mem_image_iff d z x _

private theorem moving_chart_properties
    (d : TerminalSaddleGeometry M P p e)
    (R : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    {a ε : Real}
    (hR : ∀ x ∈ closedSquare a, R x = Saddle.toE2 (d.frame (g (e x))))
    (hslice : ∀ x ∈ closedSquare a, ∀ t ∈ Icc (-ε) ε,
      Saddle.toE3 (R x) (inner Real (M.v : E3) (g p) + t) ∈ d.frame '' range g ↔
        -x 0 ^ 2 + x 1 ^ 2 = t)
    (hsource : closedSquare a ⊆ e.source)
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2) :
    ∃ Q : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
      ContDiff Real ∞ (fun z : Real × E2 => Q z.1 z.2) ∧
      ContDiff Real ∞ (fun z : Real × E2 => (Q z.1).symm z.2) ∧
      (∀ t, ∀ x ∈ closedSquare a, -x 0 ^ 2 + x 1 ^ 2 = t →
        Q t x = Saddle.toE2 (d.flatten (g (e x)))) ∧
      (∀ x ∈ closedSquare a, ∀ t ∈ Icc (-ε) ε,
        Q t x ∈ d.A (inner Real (M.v : E3) (g p) + t) ↔
          -x 0 ^ 2 + x 1 ^ 2 = t) ∧
      ∀ t x, Q t x = terminalHeightFiber d (inner Real (M.v : E3) (g p) + t) (R x) := by
  let c := inner Real (M.v : E3) (g p)
  let Q : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞ :=
    fun t => R.trans (terminalHeightFiber d (c + t))
  refine ⟨Q, ?_, ?_, ?_, ?_, fun _ _ => rfl⟩
  · exact (terminalHeightFiber_contDiff d).comp
      (f := fun z : Real × E2 => (c + z.1, R z.2))
      ((contDiff_const.add contDiff_fst).prodMk (R.contDiff.comp contDiff_snd))
  · change ContDiff Real ∞ (fun z : Real × E2 =>
      R.symm ((terminalHeightFiber d (c + z.1)).symm z.2))
    have hh : ContDiff Real ∞ (fun z : Real × E2 =>
        (terminalHeightFiber d (c + z.1)).symm z.2) :=
      (terminalHeightFiber_symm_contDiff d).comp
        (f := fun z : Real × E2 => (c + z.1, z.2))
        ((contDiff_const.add contDiff_fst).prodMk contDiff_snd)
    exact R.symm.contDiff.comp hh
  · intro t x hx hxt
    change terminalHeightFiber d (c + t) (R x) = _
    rw [terminalHeightFiber_apply]
    have hh : Saddle.toE3 (R x) (c + t) = d.frame (g (e x)) := by
      have hp := hR x hx
      have hz := d.frame_height (g (e x))
      rw [hform x (hsource hx)] at hz
      ext i
      fin_cases i
      · exact congrArg (fun y : E2 => y 0) hp
      · exact congrArg (fun y : E2 => y 1) hp
      · change c + t = d.frame (g (e x)) 2
        dsimp [c]
        linarith
    rw [hh, d.frame.symm_apply_apply]
    rfl
  · intro x hx t ht
    exact (terminalHeightFiber_mem_actual_slice_iff d (c + t) (R x)).trans (hslice x hx t ht)




theorem exists_terminal_geometry_with_matched_moving_morse_coordinates
    (M : SphereMorseReduction f) (hg : g ∈ M.tree.leaves)
    (P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g)
    (hP : P.Protects ((fun q => inner Real (M.v : E3) (M.D (f q))) ''
      {q | mfderiv (𝓡 2) 𝓘(Real, Real)
        (fun y => inner Real (M.v : E3) (M.D (f y))) q = 0}))
    (hcaps : P.PreservesCaps) (hp : p ∈ interior P.core)
    (hc : mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun q => inner Real (M.v : E3) (g q)) p = 0)
    (hunique : ∀ q ∈ P.core, mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun y => inner Real (M.v : E3) (g y)) q = 0 → q = p)
    (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (het : e.target ⊆ interior P.core)
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2) :
    ∀ nested : Bool, ∃ d : TerminalSaddleGeometry M P p e,
      d.model = (if nested then Saddle.Nested.shear (3 / 10) else Saddle.shear) ∧
      (∀ y, inner Real (M.v : E3) y = inner Real (M.v : E3) (g p) → d.D y = y) ∧
      2 * d.r < Real.sqrt d.scale * d.matchingRadius ∧
      ∃ a ε : Real, 0 < a ∧ 0 < ε ∧ 8 * d.r < a ∧ closedSquare a ⊆ e.source ∧
        ∃ Q : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
          ContDiff Real ∞ (fun z : Real × E2 => Q z.1 z.2) ∧
          ContDiff Real ∞ (fun z : Real × E2 => (Q z.1).symm z.2) ∧
          (∀ t, ∀ x ∈ closedSquare a, -x 0 ^ 2 + x 1 ^ 2 = t →
            Q t x = Saddle.toE2 (d.flatten (g (e x)))) ∧
          ∀ x ∈ closedSquare a, ∀ t ∈ Icc (-ε) ε,
            (Q t x ∈ d.A (inner Real (M.v : E3) (g p) + t) ↔
              -x 0 ^ 2 + x 1 ^ 2 = t) ∧
            (Q t x ∈ d.B (inner Real (M.v : E3) (g p) + t) ↔
              -x 0 ^ 2 + x 1 ^ 2 = t) := by
  intro nested
  have hgeometry : ∃ d : TerminalSaddleGeometry M P p e,
      d.model = (if nested then Saddle.Nested.shear (3 / 10) else Saddle.shear) ∧
      (∀ y, inner Real (M.v : E3) y = inner Real (M.v : E3) (g p) → d.D y = y) ∧
      2 * d.r < Real.sqrt d.scale * d.matchingRadius ∧
      ∃ a ε : Real, 0 < a ∧ 0 < ε ∧ 8 * d.r < a ∧ closedSquare a ⊆ e.source ∧
        ∃ R : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
          (∀ x ∈ closedSquare a, R x = Saddle.toE2 (d.frame (g (e x)))) ∧
          ∀ x ∈ closedSquare a, ∀ t ∈ Icc (-ε) ε,
            (Saddle.toE3 (R x) (inner Real (M.v : E3) (g p) + t) ∈ d.frame '' range g ↔
              -x 0 ^ 2 + x 1 ^ 2 = t) ∧
            (Saddle.toE3 (R x) (inner Real (M.v : E3) (g p) + t) ∈
              d.frame '' (d.filledModel '' sphere (0 : E3) 1) ↔
              -x 0 ^ 2 + x 1 ^ 2 = t) := by
    cases nested
    · exact exists_terminal_saddle_geometry_with_matched_planar_chart M hg P hP hcaps hp hc hunique
        e he0 hep he hei het hform
    · exact exists_terminal_nested_saddle_geometry_with_matched_planar_chart M hg P hP hcaps hp hc
        e he0 hep he hei hform
  obtain ⟨d, hmodel, hfixed, hsize, a, ε, ha, hε, hmargin, hsource, R, hR, hraw⟩ := hgeometry
  obtain ⟨Q, hQ, hQi, hpatch, hactual, hformula⟩ := moving_chart_properties d R hR
    (fun x hx t ht => (hraw x hx t ht).1) hsource hform
  refine ⟨d, hmodel, hfixed, hsize, a, ε, ha, hε, hmargin, hsource,
    Q, hQ, hQi, hpatch, ?_⟩
  intro x hx t ht
  refine ⟨hactual x hx t ht, ?_⟩
  rw [hformula, terminalHeightFiber_mem_model_slice_iff]
  exact (hraw x hx t ht).2



theorem exists_terminal_geometry_with_moving_morse_coordinates
    (M : SphereMorseReduction f) (hg : g ∈ M.tree.leaves)
    (P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g)
    (hP : P.Protects ((fun q => inner Real (M.v : E3) (M.D (f q))) ''
      {q | mfderiv (𝓡 2) 𝓘(Real, Real)
        (fun y => inner Real (M.v : E3) (M.D (f y))) q = 0}))
    (hcaps : P.PreservesCaps) (hp : p ∈ interior P.core)
    (hc : mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun q => inner Real (M.v : E3) (g q)) p = 0)
    (hunique : ∀ q ∈ P.core, mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun y => inner Real (M.v : E3) (g y)) q = 0 → q = p)
    (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (het : e.target ⊆ interior P.core)
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2) :
    ∀ nested : Bool, ∃ d : TerminalSaddleGeometry M P p e,
      d.model = (if nested then Saddle.Nested.shear (3 / 10) else Saddle.shear) ∧
      (∀ y, inner Real (M.v : E3) y = inner Real (M.v : E3) (g p) → d.D y = y) ∧
      2 * d.r < Real.sqrt d.scale * d.matchingRadius ∧
      ∃ a ε : Real, 0 < a ∧ 0 < ε ∧ 8 * d.r < a ∧ closedSquare a ⊆ e.source ∧
        ∃ Q : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
          ContDiff Real ∞ (fun z : Real × E2 => Q z.1 z.2) ∧
          ContDiff Real ∞ (fun z : Real × E2 => (Q z.1).symm z.2) ∧
          (∀ t, ∀ x ∈ closedSquare a, -x 0 ^ 2 + x 1 ^ 2 = t →
            Q t x = Saddle.toE2 (d.flatten (g (e x)))) ∧
          ∀ x ∈ closedSquare a, ∀ t ∈ Icc (-ε) ε,
            Q t x ∈ d.A (inner Real (M.v : E3) (g p) + t) ↔
              -x 0 ^ 2 + x 1 ^ 2 = t := by
  intro nested
  obtain ⟨d, hm, hf, hs, a, ε, ha, hε, hmargin, hsource, Q, hQ, hQi, hpatch, hslice⟩ :=
    exists_terminal_geometry_with_matched_moving_morse_coordinates M hg P hP hcaps hp hc hunique
      he0 hep he hei het hform nested
  exact ⟨d, hm, hf, hs, a, ε, ha, hε, hmargin, hsource, Q, hQ, hQi, hpatch,
    fun x hx t ht => (hslice x hx t ht).1⟩

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
