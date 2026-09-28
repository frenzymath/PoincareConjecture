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
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

open SaddleLevel

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}

theorem exists_terminal_spatially_protected_morse_square
    (d : TerminalSaddleGeometry M P p e)
    (hsize : 2 * d.r < Real.sqrt d.scale * d.matchingRadius)
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2)
    {δ : Real} (hδ : 0 < δ) (C : Set E2) (V : Set E3)
    (hpatch : (d.flatten ∘ g) '' (e '' closedSquare d.r) ⊆ V)
    (hfiber : ∀ t ∈ Icc (-δ) δ, ∀ x : E2,
      Saddle.toE3 x (inner Real (M.v : E3) (g p) + t) ∈ V → x ∈ C)
    (O : Set E2) (hO : IsOpen O) (hCO : C ⊆ O) :
    ∃ ρ : Real, 0 < ρ ∧ ρ ≤ d.r ∧ ρ ^ 2 ≤ δ ∧
      closedSquare ρ ⊆ e.source ∧
      (∀ x ∈ closedSquare ρ,
        (Real.sqrt d.scale)⁻¹ • x ∈ closedBall (0 : E2) d.matchingRadius) ∧
      IsOpen (Saddle.toE2 ⁻¹' O) ∧
      (d.flatten ∘ g ∘ e) '' closedSquare ρ ⊆ Saddle.toE2 ⁻¹' O := by
  let ρ := min d.r (Real.sqrt δ / 2)
  have hρ : 0 < ρ := lt_min d.r_pos (half_pos (Real.sqrt_pos.mpr hδ))
  have hρr : ρ ≤ d.r := min_le_left _ _
  have hρδ : ρ ^ 2 ≤ δ := by
    have hle : ρ ≤ Real.sqrt δ / 2 := min_le_right _ _
    have hs := Real.sq_sqrt hδ.le
    have hp := Real.sqrt_nonneg δ
    nlinarith
  have hsquare : closedSquare ρ ⊆ closedSquare d.r :=
    fun x hx => ⟨hx.1.trans hρr, hx.2.trans hρr⟩
  have hsource : closedSquare ρ ⊆ e.source := hsquare.trans d.square_source
  have hproj : Continuous Saddle.toE2 := by
    apply ContDiff.continuous (n := ∞) (𝕜 := Real)
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · exact (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 3)).contDiff
    · exact (EuclideanSpace.proj (𝕜 := Real) (1 : Fin 3)).contDiff
  refine ⟨ρ, hρ, hρr, hρδ, hsource, ?_, hO.preimage hproj, ?_⟩
  · intro x hx
    have hk := Real.sqrt_pos.mpr d.scale_pos
    have hn : ‖x‖ ≤ 2 * d.r :=
      mem_closedBall_zero_iff.mp (closedSquare_subset_closedBall d.r_pos.le (hsquare hx))
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hk), ← div_eq_inv_mul]
    apply (div_le_iff₀ hk).mpr
    simpa only [mul_comm] using (hn.trans hsize.le)
  · rintro y ⟨x, hx, rfl⟩
    let t := -(x 0)^2 + (x 1)^2
    have h0 : (x 0)^2 ≤ ρ ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (x 0)) hρ.le).mpr hx.1
    have h1 : (x 1)^2 ≤ ρ ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (x 1)) hρ.le).mpr hx.2
    have ht : t ∈ Icc (-δ) δ := by
      dsimp [t]
      constructor <;> nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
    have hyV : d.flatten (g (e x)) ∈ V :=
      hpatch (mem_image_of_mem (d.flatten ∘ g) (mem_image_of_mem e (hsquare hx)))
    have hyheight : d.flatten (g (e x)) 2 = inner Real (M.v : E3) (g p) + t := by
      change d.frame (d.D (g (e x))) 2 = _
      rw [d.frame_height, d.D_height, hform x (hsource hx)]
      dsimp [t]
      ring
    have hlift : Saddle.toE3 (Saddle.toE2 (d.flatten (g (e x))))
        (inner Real (M.v : E3) (g p) + t) = d.flatten (g (e x)) := by
      ext i
      fin_cases i <;> simp [Saddle.toE2, Saddle.toE3, hyheight]
    apply hCO
    apply hfiber t ht
    simpa only [comp_def, hlift] using hyV

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

end

end M38Schoenflies
