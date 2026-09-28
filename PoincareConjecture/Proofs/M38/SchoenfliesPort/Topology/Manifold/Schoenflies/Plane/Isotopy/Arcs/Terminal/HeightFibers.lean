import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.TerminalData







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

private theorem projection_lift (x : E2) (z : Real) :
    Saddle.toE2 (Saddle.toE3 x z) = x := by
  ext i
  fin_cases i <;> rfl

private theorem lift_projection {y : E3} {z : Real} (hy : y 2 = z) :
    Saddle.toE3 (Saddle.toE2 y) z = y := by
  ext i
  fin_cases i <;> simp [Saddle.toE2, Saddle.toE3, hy]

private theorem smooth_projection : ContDiff Real ∞ Saddle.toE2 := by
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i
  · exact (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 3)).contDiff
  · exact (EuclideanSpace.proj (𝕜 := Real) (1 : Fin 3)).contDiff

private theorem smooth_lift :
    ContDiff Real ∞ (fun q : Real × E2 => Saddle.toE3 q.2 q.1) := by
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i
  · exact (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 2)).contDiff.comp contDiff_snd
  · exact (EuclideanSpace.proj (𝕜 := Real) (1 : Fin 2)).contDiff.comp contDiff_snd
  · exact contDiff_fst

private def planarHeightFiber
    (G : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hG : ∀ y, G y 2 = y 2) (z : Real) :
    Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞ where
  toFun x := Saddle.toE2 (G (Saddle.toE3 x z))
  invFun x := Saddle.toE2 (G.symm (Saddle.toE3 x z))
  left_inv x := by
    change Saddle.toE2 (G.symm (Saddle.toE3 (Saddle.toE2 (G (Saddle.toE3 x z))) z)) = x
    have hg : G (Saddle.toE3 x z) 2 = z := hG _
    rw [lift_projection hg, G.symm_apply_apply, projection_lift]
  right_inv x := by
    change Saddle.toE2 (G (Saddle.toE3 (Saddle.toE2 (G.symm (Saddle.toE3 x z))) z)) = x
    have hGi : G.symm (Saddle.toE3 x z) 2 = z := by
      have hh := (hG (G.symm (Saddle.toE3 x z))).symm
      rw [G.apply_symm_apply] at hh
      exact hh
    rw [lift_projection hGi, G.apply_symm_apply, projection_lift]
  contMDiff_toFun := (smooth_projection.comp
    (G.contDiff.comp (smooth_lift.comp (contDiff_const.prodMk contDiff_id)))).contMDiff
  contMDiff_invFun := (smooth_projection.comp
    (G.symm.contDiff.comp (smooth_lift.comp (contDiff_const.prodMk contDiff_id)))).contMDiff

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}

private def framedFlattening (d : TerminalSaddleGeometry M P p e) :
    Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞ := (d.frame.symm.trans d.D).trans d.frame

private theorem framedFlattening_height (d : TerminalSaddleGeometry M P p e) (y : E3) :
    framedFlattening d y 2 = y 2 := by
  change d.frame (d.D (d.frame.symm y)) 2 = y 2
  rw [d.frame_height, d.D_height, ← d.frame_height, d.frame.apply_symm_apply]



def terminalHeightFiber (d : TerminalSaddleGeometry M P p e) (z : Real) :
    Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞ :=
  planarHeightFiber (framedFlattening d) (framedFlattening_height d) z

theorem terminalHeightFiber_apply (d : TerminalSaddleGeometry M P p e) (z : Real) (x : E2) :
    terminalHeightFiber d z x =
      Saddle.toE2 (d.frame (d.D (d.frame.symm (Saddle.toE3 x z)))) := rfl

theorem terminalHeightFiber_symm_apply
    (d : TerminalSaddleGeometry M P p e) (z : Real) (x : E2) :
    (terminalHeightFiber d z).symm x =
      Saddle.toE2 (d.frame (d.D.symm (d.frame.symm (Saddle.toE3 x z)))) := rfl


theorem terminalHeightFiber_contDiff (d : TerminalSaddleGeometry M P p e) :
    ContDiff Real ∞ (fun q : Real × E2 => terminalHeightFiber d q.1 q.2) :=
  smooth_projection.comp ((framedFlattening d).contDiff.comp smooth_lift)


theorem terminalHeightFiber_symm_contDiff (d : TerminalSaddleGeometry M P p e) :
    ContDiff Real ∞ (fun q : Real × E2 => (terminalHeightFiber d q.1).symm q.2) :=
  smooth_projection.comp ((framedFlattening d).symm.contDiff.comp smooth_lift)


theorem terminalHeightFiber_lift (d : TerminalSaddleGeometry M P p e) (z : Real) (x : E2) :
    Saddle.toE3 (terminalHeightFiber d z x) z =
      d.frame (d.D (d.frame.symm (Saddle.toE3 x z))) :=
  lift_projection (framedFlattening_height d (Saddle.toE3 x z))



theorem terminalHeightFiber_eq_id_of_fixed_plane
    (d : TerminalSaddleGeometry M P p e) {c : Real}
    (hfix : ∀ y : E3, inner Real (M.v : E3) y = c → d.D y = y) :
    ∀ x : E2, terminalHeightFiber d c x = x := by
  intro x
  rw [terminalHeightFiber_apply, hfix]
  · rw [d.frame.apply_symm_apply, projection_lift]
  · rw [← d.frame_height, d.frame.apply_symm_apply]
    rfl

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

end

end M38Schoenflies
