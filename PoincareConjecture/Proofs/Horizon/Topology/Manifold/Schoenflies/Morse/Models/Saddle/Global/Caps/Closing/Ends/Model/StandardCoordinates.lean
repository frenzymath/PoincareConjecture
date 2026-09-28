import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.Model.Charts
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.MorseCoordinates

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing.Model

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

private theorem exists_north_coordinates (p : S2)
    (hx : (p : E3) 0 = 0) (hy : (p : E3) 1 = 0) (hz : (p : E3) 2 = 1) :
    ∃ e : OpenPartialHomeomorph E2 S2, ∃ σ : Fin 2 → Real,
      (∀ i, σ i = -1 ∨ σ i = 1) ∧ 0 ∈ e.source ∧ e 0 = p ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target ∧
      ∀ x ∈ e.source, Saddle.height (e x) =
        Saddle.height p + ∑ i : Fin 2, σ i * x i ^ 2 := by
  let U := ball (0 : E2) 1
  let R : E2 → Real := fun x => Real.sqrt (1-‖x‖^2)
  let B : E2 → Real := fun x => -(1+R x)⁻¹
  let A : E2 → Real := fun x => B x-1
  let H : E2 → Real := fun x => R x-(x 0)^2
  have hrad (x : E2) (hx : x ∈ U) : 0 < 1-‖x‖^2 := by
    have hh := mem_ball_zero_iff.mp hx
    nlinarith [norm_nonneg x]
  have hR : ContDiffOn Real ∞ R U :=
    (contDiff_const.sub (contDiff_id.norm_sq Real)).contDiffOn.sqrt
      (fun x hx => (hrad x hx).ne')
  have hB : ContDiffOn Real ∞ B U :=
    ((contDiffOn_const.add hR).inv (fun x _ => by
      have := Real.sqrt_nonneg (1-‖x‖^2)
      dsimp [R]
      linarith)).neg
  have hA : ContDiffOn Real ∞ A U := hB.sub contDiffOn_const
  have hform (x : E2) (hx : x ∈ U) : H x = 1+A x*(x 0)^2+B x*(x 1)^2 := by
    have hRsq : (R x)^2 = 1-‖x‖^2 := Real.sq_sqrt (hrad x hx).le
    have hden : 1+R x ≠ 0 := by have := Real.sqrt_nonneg (1-‖x‖^2); dsimp [R]; linarith
    have hd : R x-1 = -‖x‖^2/(1+R x) := by
      apply (eq_div_iff hden).mpr
      nlinarith [hRsq]
    rw [Saddle.norm_sq_two] at hd
    dsimp [H, A, B]
    field_simp at hd ⊢
    nlinarith [hd]
  obtain ⟨Q, s, t, hs, ht, hQ0, hQz, hQU, hQ, hQi, hQform⟩ :=
    exists_signed_square_coordinates_of_factors (U := U) isOpen_ball
      (mem_ball_self zero_lt_one) hA hB
      (by norm_num [A, B, R]) (by norm_num [B, R]) hform
  let C := Saddle.lowerSphereChart.trans (sphereCoordinateReflection 2).toHomeomorph.toOpenPartialHomeomorph
  have hC0 : C 0 = p := by
    apply Subtype.ext
    ext i
    change (sphereCoordinateReflection 2 (Saddle.lowerSphereChart 0) : E3) i = (p : E3) i
    rw [sphereCoordinateReflection_apply, Saddle.lowerSphereChart_zero]
    fin_cases i <;> simp [Saddle.saddlePoint, hx, hy, hz]
  have hCform (x : E2) (hx : x ∈ U) : Saddle.height (C x) = H x := by
    rw [Saddle.height_apply]
    change (sphereCoordinateReflection 2 (Saddle.lowerSphereChart x) : E3) 2 -
      ((sphereCoordinateReflection 2 (Saddle.lowerSphereChart x) : E3) 0)^2 = _
    rw [sphereCoordinateReflection_apply, sphereCoordinateReflection_apply,
      Saddle.lowerSphereChart_coe hx]
    simp [Saddle.lowerSphereGraph, H, R]
  let e := Q.trans C
  let σ : Fin 2 → Real := ![s, t]
  refine ⟨e, σ, ?_, ⟨hQ0, hQU hQ0, mem_univ _⟩,
    by change C (Q 0) = p; rw [hQz, hC0], ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact hs
    · exact ht
  · exact (sphereCoordinateReflection 2).contMDiff.comp_contMDiffOn
      (Saddle.lowerSphereChart_smooth.comp (hQ.contMDiffOn.mono inter_subset_left)
        (fun _ hx => hx.2.1))
  · exact hQi.contMDiffOn.comp
      ((Saddle.lowerSphereChart_symm_smooth.comp (sphereCoordinateReflection 2).symm.contMDiff).contMDiffOn)
      (fun _ hx => hx.2)
  · intro x hx
    change Saddle.height (C (Q x)) = _
    rw [hCform _ (hQU hx.1), hQform x hx.1, Saddle.height_apply]
    simp only [σ, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, hz]
    rw [show (p : E3) 0 = 0 from ‹(p : E3) 0 = 0›]
    ring

theorem exists_standard_critical_coordinates (p : S2)
    (hp : mfderiv (𝓡 2) 𝓘(Real, Real) Saddle.height p = 0) :
    ∃ e : OpenPartialHomeomorph E2 S2, ∃ σ : Fin 2 → Real,
      (∀ i, σ i = -1 ∨ σ i = 1) ∧ 0 ∈ e.source ∧ e 0 = p ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target ∧
      ∀ x ∈ e.source, Saddle.height (e x) =
        Saddle.height p + ∑ i : Fin 2, σ i * x i ^ 2 := by
  classical
  obtain ⟨hy, hx | hz⟩ := (Saddle.height_critical_iff p).mp hp
  · have hsq : ((p : E3) 2)^2 = 1 := by
      have hn := EuclideanSpace.norm_sq_eq (p : E3)
      simp [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs, hx, hy] at hn
      nlinarith
    rcases sq_eq_one_iff.mp hsq with hz | hz
    · exact exists_north_coordinates p hx hy hz
    · have heq : p = Saddle.saddlePoint := by
        apply Subtype.ext
        ext i
        fin_cases i <;> simp [Saddle.saddlePoint, hx, hy, hz]
      subst p
      obtain ⟨e, he0, hep, he, hei, hform⟩ := Saddle.exists_saddle_coordinates
      refine ⟨e, ![-1, 1], ?_, he0, hep, he, hei, ?_⟩
      · intro i
        fin_cases i <;> simp
      · intro x hx
        rw [hform x hx, Saddle.height_saddlePoint]
        simp [Fin.sum_univ_two]
        ring
  · have hn : ((p : E3) 0)^2 = 3/4 := by
      have hh := EuclideanSpace.norm_sq_eq (p : E3)
      simp [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs, hy, hz] at hh
      nlinarith
    have hx : (p : E3) 0 ≠ 0 := by intro hh; rw [hh] at hn; norm_num at hn
    let positive : Bool := decide (0 < (p : E3) 0)
    let C := meridianSphereChart positive (-1/2)
    have hroot : Saddle.Nested.meridianRoot (-1/2) = |(p : E3) 0| := by
      unfold Saddle.Nested.meridianRoot
      rw [show (1-(-1/2 : Real)^2) = ((p : E3) 0)^2 by linarith, Real.sqrt_sq_eq_abs]
    have hxroot : (if positive then Saddle.Nested.meridianRoot (-1/2)
        else -Saddle.Nested.meridianRoot (-1/2)) = (p : E3) 0 := by
      rw [hroot]
      by_cases hpos : 0 < (p : E3) 0
      · simp [positive, hpos, abs_of_pos hpos]
      · simp [positive, hpos, abs_of_neg (lt_of_le_of_ne (le_of_not_gt hpos) hx)]
    have hC0 : C 0 = p := by
      apply Subtype.ext
      rw [meridianSphereChart_zero positive (by norm_num), hxroot]
      ext i
      fin_cases i <;> simp [hy, hz]
    refine ⟨C, fun _ => 1, fun _ => Or.inr rfl, ?_, hC0,
      meridianSphereChart_smooth _ _, meridianSphereChart_symm_smooth _ _, ?_⟩
    · rw [meridianSphereChart_source]
      norm_num [Saddle.Nested.coordinateDomain]
    · intro x hxC
      have hxc := meridianSphereChart_source positive (-1/2) ▸ hxC
      rw [standard_height_meridianSphereChart positive hxc, Saddle.height_apply, hz, hn]
      simp only [Fin.sum_univ_two, one_mul]
      ring

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing.Model
