import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.Model.Charts



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing.Model

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1
open Saddle.Nested

theorem exists_nested_critical_coordinates (p : S2)
    (hp : mfderiv (𝓡 2) 𝓘(Real, Real) Saddle.Nested.height p = 0) :
    ∃ e : OpenPartialHomeomorph E2 S2, ∃ σ : Fin 2 → Real,
      (∀ i, σ i = -1 ∨ σ i = 1) ∧ 0 ∈ e.source ∧ e 0 = p ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target ∧
      ∀ x ∈ e.source, Saddle.Nested.height (e x) =
        Saddle.Nested.height p + ∑ i : Fin 2, σ i * x i ^ 2 := by
  classical
  obtain ⟨hy, hc⟩ := critical_point_coordinates hp
  have hn : ((p : E3) 0)^2 = 1-((p : E3) 2)^2 := by
    have hh := EuclideanSpace.norm_sq_eq (p : E3)
    simp [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs, hy] at hh
    linarith
  have hx : (p : E3) 0 ≠ 0 := by
    intro hx
    rw [hx] at hc
    have hz : (p : E3) 2 = 0 := by linarith
    rw [hx, hz] at hn
    norm_num at hn
  have hz : 0 < 1-((p : E3) 2)^2 := by nlinarith [sq_pos_of_ne_zero hx]
  let positive : Bool := decide (0 < (p : E3) 0)
  let a : Real := if positive then 3/10 else -(3/10)
  have ha : a = -(3/10 : Real) ∨ a = 3/10 := by
    dsimp [a]
    split_ifs <;> simp
  have hroot : meridianRoot ((p : E3) 2) = |(p : E3) 0| := by
    unfold meridianRoot
    rw [← hn, Real.sqrt_sq_eq_abs]
  have hxroot : (if positive then meridianRoot ((p : E3) 2)
      else -meridianRoot ((p : E3) 2)) = (p : E3) 0 := by
    rw [hroot]
    by_cases hpos : 0 < (p : E3) 0
    · simp [positive, hpos, abs_of_pos hpos]
    · simp [positive, hpos, abs_of_neg (lt_of_le_of_ne (le_of_not_gt hpos) hx)]
  have hcrit : meridianRoot ((p : E3) 2) * (2*(p : E3) 2-1) = -a*(p : E3) 2 := by
    rw [hroot]
    by_cases hpos : 0 < (p : E3) 0
    · simp only [a, positive, hpos, decide_true, ↓reduceIte, abs_of_pos hpos]
      linarith
    · simp only [a, positive, hpos, decide_false, Bool.false_eq_true, ↓reduceIte,
        abs_of_neg (lt_of_le_of_ne (le_of_not_gt hpos) hx)]
      nlinarith
  let C := meridianSphereChart positive ((p : E3) 2)
  have hC0 : C 0 = p := by
    apply Subtype.ext
    rw [meridianSphereChart_zero positive hz, hxroot]
    ext i
    fin_cases i <;> simp [hy]
  obtain ⟨Q, s, t, hs, ht, hQ0, hQz, hQU, hQ, hQi, hform⟩ :=
    exists_nested_meridian_square_coordinates ha hz hcrit
  let e := Q.trans C
  have he (x : E2) : e x = C (Q x) := rfl
  have hCs : C.source = coordinateDomain ((p : E3) 2) := meridianSphereChart_source _ _
  let σ : Fin 2 → Real := ![s, t]
  refine ⟨e, σ, ?_, ⟨hQ0, hCs ▸ hQU hQ0⟩,
    by rw [he, hQz, hC0], ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact hs
    · exact ht
  · exact (meridianSphereChart_smooth positive _).comp
      (hQ.contMDiffOn.mono inter_subset_left) (fun _ hx => hx.2)
  · exact hQi.contMDiffOn.comp ((meridianSphereChart_symm_smooth positive _).mono inter_subset_left)
      (fun _ hx => hx.2)
  · intro x hx
    have hbase : meridianHeight a ((p : E3) 2) 0 = Saddle.Nested.height p := by
      rw [← nested_height_meridianSphereChart positive (by simpa [coordinateDomain] using hz)]
      exact congrArg Saddle.Nested.height hC0
    change Saddle.Nested.height (C (Q x)) = _
    rw [nested_height_meridianSphereChart positive (hQU hx.1), hform x hx.1, hbase]
    simp only [σ, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing.Model
