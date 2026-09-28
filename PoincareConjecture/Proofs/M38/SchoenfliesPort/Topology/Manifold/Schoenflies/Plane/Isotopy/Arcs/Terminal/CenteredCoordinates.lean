import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.StationarySlices

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

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}

def terminalCenteredFrame (d : TerminalSaddleGeometry M P p e) :
    Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞ where
  toFun y := d.frame y - inner Real (M.v : E3) (g p) • EuclideanSpace.single 2 1
  invFun y := d.frame.symm (y + inner Real (M.v : E3) (g p) • EuclideanSpace.single 2 1)
  left_inv y := by simp
  right_inv y := by simp
  contMDiff_toFun := (d.frame.contDiff.sub contDiff_const).contMDiff
  contMDiff_invFun := (d.frame.symm.contDiff.comp (contDiff_id.add contDiff_const)).contMDiff

theorem terminalCenteredFrame_apply (d : TerminalSaddleGeometry M P p e) (y : E3) :
    terminalCenteredFrame d y =
      d.frame y - inner Real (M.v : E3) (g p) • EuclideanSpace.single 2 1 := rfl

theorem terminalCenteredFrame_height (d : TerminalSaddleGeometry M P p e) (y : E3) :
    terminalCenteredFrame d y 2 = inner Real (M.v : E3) y - inner Real (M.v : E3) (g p) := by
  simp [terminalCenteredFrame_apply, PiLp.sub_apply, PiLp.smul_apply, d.frame_height]

theorem terminalCenteredFrame_projection (d : TerminalSaddleGeometry M P p e) (y : E3) :
    Saddle.toE2 (terminalCenteredFrame d y) = Saddle.toE2 (d.frame y) := by
  ext i
  fin_cases i <;> simp [terminalCenteredFrame_apply, Saddle.toE2, PiLp.sub_apply, PiLp.smul_apply]

theorem terminal_frame_translate (d : TerminalSaddleGeometry M P p e) (y : E3) (t : Real) :
    d.frame (y + t • (M.v : E3)) = d.frame y + t • EuclideanSpace.single 2 1 := by
  let J₀ : E3 ≃ᵢ E3 := { d.frame.toEquiv with isometry_toFun := d.frame_isometry }
  let J := J₀.toRealLinearIsometryEquivOfMapZero d.frame_zero
  have hJ (x : E3) : J x = d.frame x := rfl
  have hJv : J (M.v : E3) = EuclideanSpace.single 2 1 := by
    apply ext_inner_right Real
    intro x
    obtain ⟨z, rfl⟩ := J.surjective x
    rw [J.inner_map_map]
    simpa [PiLp.inner_apply, hJ] using (d.frame_height z).symm
  change J (y + t • (M.v : E3)) = J y + _
  rw [map_add, map_smul, hJv]

theorem terminalCenteredFrame_translate (d : TerminalSaddleGeometry M P p e)
    (y : E3) (t : Real) :
    terminalCenteredFrame d (y + t • (M.v : E3)) =
      terminalCenteredFrame d y + t • EuclideanSpace.single 2 1 := by
  change d.frame (y + t • (M.v : E3)) - _ = (d.frame y - _) + _
  rw [terminal_frame_translate]
  abel

def terminalCenteredFlattening (d : TerminalSaddleGeometry M P p e) :
    Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞ :=
  ((terminalCenteredFrame d).symm.trans d.D).trans (terminalCenteredFrame d)

def terminalCenteredModel (d : TerminalSaddleGeometry M P p e) :
    Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞ := d.filledModel.trans (terminalCenteredFrame d)

theorem terminalCenteredFlattening_height (d : TerminalSaddleGeometry M P p e) (y : E3) :
    terminalCenteredFlattening d y 2 = y 2 := by
  change terminalCenteredFrame d (d.D ((terminalCenteredFrame d).symm y)) 2 = y 2
  rw [terminalCenteredFrame_height, d.D_height, ← terminalCenteredFrame_height,
    Diffeomorph.apply_symm_apply]

theorem terminalCenteredFlattening_apply_frame (d : TerminalSaddleGeometry M P p e)
    (y : E3) : terminalCenteredFlattening d (terminalCenteredFrame d y) =
      terminalCenteredFrame d (d.D y) := by
  change terminalCenteredFrame d (d.D ((terminalCenteredFrame d).symm
    (terminalCenteredFrame d y))) = _
  rw [Diffeomorph.symm_apply_apply]

theorem terminalCenteredFlattening_zero (d : TerminalSaddleGeometry M P p e)
    (hzero : ∀ y, inner Real (M.v : E3) y = inner Real (M.v : E3) (g p) → d.D y = y)
    (y : E3) (hy : y 2 = 0) : terminalCenteredFlattening d y = y := by
  obtain ⟨x, rfl⟩ := (terminalCenteredFrame d).surjective y
  change terminalCenteredFrame d x 2 = 0 at hy
  change terminalCenteredFlattening d (terminalCenteredFrame d x) = terminalCenteredFrame d x
  rw [terminalCenteredFrame_height] at hy
  rw [terminalCenteredFlattening_apply_frame, hzero x (sub_eq_zero.mp hy)]

theorem terminalCenteredFrame_eq_lift_iff (d : TerminalSaddleGeometry M P p e)
    (y : E3) (x : E2) (t : Real) :
    terminalCenteredFrame d y = Saddle.toE3 x t ↔
      d.frame y = Saddle.toE3 x (inner Real (M.v : E3) (g p) + t) := by
  constructor
  · intro h
    rw [terminalCenteredFrame_apply] at h
    ext i
    fin_cases i
    · simpa [Saddle.toE3, PiLp.sub_apply, PiLp.smul_apply] using
        congrArg (fun q : E3 => q 0) h
    · simpa [Saddle.toE3, PiLp.sub_apply, PiLp.smul_apply] using
        congrArg (fun q : E3 => q 1) h
    · have hh := congrArg (fun q : E3 => q 2) h
      simp [Saddle.toE3, PiLp.sub_apply, PiLp.smul_apply] at hh ⊢
      linarith
  · intro h
    change d.frame y - _ = _
    rw [h]
    ext i
    fin_cases i <;> simp [Saddle.toE3, PiLp.sub_apply, PiLp.smul_apply]

theorem terminalCenteredFlattening_actual_fiber (d : TerminalSaddleGeometry M P p e)
    (t : Real) :
    {x : E2 | Saddle.toE3 x t ∈ range
      (fun q => terminalCenteredFlattening d (terminalCenteredFrame d (g q)))} =
      d.A (inner Real (M.v : E3) (g p) + t) := by
  ext x
  constructor
  · rintro ⟨q, hq⟩
    change terminalCenteredFlattening d (terminalCenteredFrame d (g q)) = _ at hq
    rw [terminalCenteredFlattening_apply_frame] at hq
    exact ⟨g q, mem_range_self q, (terminalCenteredFrame_eq_lift_iff d _ x t).mp hq⟩
  · rintro ⟨_, ⟨q, rfl⟩, hq⟩
    refine ⟨q, ?_⟩
    change terminalCenteredFlattening d (terminalCenteredFrame d (g q)) = _
    rw [terminalCenteredFlattening_apply_frame]
    exact (terminalCenteredFrame_eq_lift_iff d _ x t).mpr hq

theorem terminalCenteredFlattening_model_fiber (d : TerminalSaddleGeometry M P p e)
    (t : Real) :
    {x : E2 | Saddle.toE3 x t ∈ ((terminalCenteredModel d).trans
      (terminalCenteredFlattening d)) '' sphere (0 : E3) 1} =
      d.B (inner Real (M.v : E3) (g p) + t) := by
  ext x
  constructor
  · rintro ⟨q, hq, heq⟩
    change terminalCenteredFlattening d (terminalCenteredFrame d (d.filledModel q)) = _ at heq
    rw [terminalCenteredFlattening_apply_frame] at heq
    exact ⟨d.filledModel q, ⟨q, hq, rfl⟩,
      (terminalCenteredFrame_eq_lift_iff d _ x t).mp heq⟩
  · rintro ⟨_, ⟨q, hq, rfl⟩, heq⟩
    refine ⟨q, hq, ?_⟩
    change terminalCenteredFlattening d (terminalCenteredFrame d (d.filledModel q)) = _
    rw [terminalCenteredFlattening_apply_frame]
    exact (terminalCenteredFrame_eq_lift_iff d _ x t).mpr heq

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

end

end M38Schoenflies
