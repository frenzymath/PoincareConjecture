import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.TerminalData
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Coordinates.Critical
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.Morse.SignedSquares







open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.Poincare.Manifold.Schoenflies.Saddle
open _root_.PoincareConjecture

namespace M38Schoenflies



noncomputable section
set_option autoImplicit false
open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing
open SaddleLevel
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}

theorem terminal_model_height_eventually_quadratic
    (d : TerminalSaddleGeometry M P p e) :
    (fun x : E2 => inner Real (M.v : E3) (d.filledModel (d.modelChart x)))
      =ᶠ[𝓝 0] (fun x => inner Real (M.v : E3) (g p) +
        d.scale * (-(x 0)^2 + (x 1)^2)) := by
  let u : E2 → E2 := fun x => Real.sqrt d.scale • x
  let t : E2 → Real := fun x => -(u x 0)^2 + (u x 1)^2
  have hzero (i : Fin 2) : Tendsto (fun x => |u x i|) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun x => |u x i|) := by dsimp [u]; fun_prop
    simpa [u] using hc.continuousAt.tendsto (x := (0 : E2))
  have ht : Tendsto (fun x => |t x|) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun x => |t x|) := by dsimp [t, u]; fun_prop
    simpa [t, u] using hc.continuousAt.tendsto (x := (0 : E2))
  filter_upwards [(hzero 0).eventually_lt_const d.r_pos,
    (hzero 1).eventually_lt_const d.r_pos,
    ht.eventually_lt_const d.delta_pos,
    closedBall_mem_nhds (0 : E2) d.matchingRadius_pos] with x hx0 hx1 hxt hx
  have hs : u x ∈ closedSquare d.r := ⟨hx0.le, hx1.le⟩
  have hi : t x ∈ Icc (-d.delta) d.delta :=
    ⟨(abs_lt.mp hxt).1.le, (abs_lt.mp hxt).2.le⟩
  have hm : (d.D ∘ g ∘ e) (u x) ∈
      (d.D ∘ g) '' {q | inner Real (M.v : E3) (g q) =
        inner Real (M.v : E3) (g p) + t x} := by
    rw [(d.flattened_levels (t x) hi).2.1]
    exact Or.inl ⟨u x, ⟨hs, rfl⟩, rfl⟩
  obtain ⟨q, hq, heq⟩ := hm
  have hheight := congrArg (fun y => inner Real (M.v : E3) y) heq
  simp only [Function.comp_apply, d.D_height] at hheight
  change inner Real (M.v : E3) (d.transport (d.model (d.modelChart x))) = _
  rw [d.matching x hx, ← hheight, hq]
  dsimp [t, u]
  simp only [mul_pow, Real.sq_sqrt d.scale_pos.le]
  ring

theorem exists_critical_in_terminal_model_band_interior
    (d : TerminalSaddleGeometry M P p e) :
    ∃ q : S2, inner Real (M.v : E3) (d.filledModel q) ∈
      Ioo d.ends.lowerCut d.ends.upperCut ∧
      mfderiv (𝓡 2) 𝓘(Real, Real)
        (fun y : S2 => inner Real (M.v : E3) (d.filledModel y)) q = 0 := by
  refine ⟨d.modelChart 0, ?_, ?_⟩
  · change inner Real (M.v : E3) (d.transport (d.model (d.modelChart 0))) ∈ _
    rw [d.transport_height]
    simp only [sub_self, mul_zero, add_zero]
    rw [d.lowerCut_eq, d.upperCut_eq]
    constructor <;> linarith [d.eta_pos]
  · have hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞
        (fun y : S2 => inner Real (M.v : E3) (d.filledModel y)) :=
      (innerSL Real (M.v : E3)).contMDiff.comp
        (d.filledModel.contMDiff.comp contMDiff_coe_sphere)
    let σ : Fin 2 → Real := ![-d.scale, d.scale]
    have hlocal := terminal_model_height_eventually_quadratic d
    have heq : (fun y : S2 => inner Real (M.v : E3) (d.filledModel y)) ∘ d.modelChart
        =ᶠ[𝓝 (0 : E2)] (fun x => inner Real (M.v : E3) (g p) +
          ∑ i : Fin 2, σ i * x i ^ 2) := by
      filter_upwards [hlocal] with x hx
      simp only [Function.comp_apply]
      rw [hx]
      simp only [σ, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      ring
    rw [mfderiv_eq_zero_iff_fderiv_of_sphere_coordinates_eventuallyEq hh d.modelChart
      d.modelChart_smooth d.modelChart_symm_smooth d.modelChart_zero heq]
    exact (Poincare.Analysis.Calculus.Morse.fderiv_diagonal_quadratic_eq_zero_iff
      _ σ (by intro i; fin_cases i <;> simp [σ, ne_of_gt d.scale_pos]) 0).mpr rfl

theorem exists_critical_in_terminal_model_band
    (d : TerminalSaddleGeometry M P p e) :
    ∃ q : S2, inner Real (M.v : E3) (d.filledModel q) ∈ d.I ∧
      mfderiv (𝓡 2) 𝓘(Real, Real)
        (fun y : S2 => inner Real (M.v : E3) (d.filledModel y)) q = 0 := by
  obtain ⟨q, hq, hc⟩ := exists_critical_in_terminal_model_band_interior d
  exact ⟨q, ⟨hq.1.le, hq.2.le⟩, hc⟩

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

end

end M38Schoenflies
