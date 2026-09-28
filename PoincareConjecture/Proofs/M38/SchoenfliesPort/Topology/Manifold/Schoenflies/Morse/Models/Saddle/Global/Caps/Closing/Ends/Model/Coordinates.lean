import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.ModelDomain
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.Model.StandardCoordinates
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.Model.NestedCoordinates

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.Poincare.Manifold.Schoenflies.Saddle
open _root_.Poincare.Manifold.Schoenflies.Saddle.Caps
open _root_.Poincare.Manifold.Schoenflies.Saddle.Caps.Closing
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1
open SaddleLevel

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}

theorem exists_terminal_model_critical_coordinates
    (data : TerminalSaddleData M P p e) (q : S2)
    (hq : mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun y : S2 => inner Real (M.v : E3)
        (data.toTerminalSaddleGeometry.filledModel y)) q = 0) :
    ∃ C : OpenPartialHomeomorph E2 S2, ∃ σ : Fin 2 → Real,
      (∀ j, σ j = -1 ∨ σ j = 1) ∧ 0 ∈ C.source ∧ C 0 = q ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ C C.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ C.symm C.target ∧
      ∀ x ∈ C.source,
        inner Real (M.v : E3) (data.toTerminalSaddleGeometry.filledModel (C x)) =
          inner Real (M.v : E3) (data.toTerminalSaddleGeometry.filledModel q) +
            ∑ j : Fin 2, σ j * x j ^ 2 := by
  have hc := (terminal_model_critical_iff data q).mp hq
  obtain ⟨C, σ, hσ, hC0, hCq, hC, hCi, hform⟩ :
      ∃ C : OpenPartialHomeomorph E2 S2, ∃ σ : Fin 2 → Real,
        (∀ j, σ j = -1 ∨ σ j = 1) ∧ 0 ∈ C.source ∧ C 0 = q ∧
        ContMDiffOn (𝓡 2) (𝓡 2) ∞ C C.source ∧
        ContMDiffOn (𝓡 2) (𝓡 2) ∞ C.symm C.target ∧
        ∀ x ∈ C.source, data.model (C x) 2 = data.model q 2 +
          ∑ j : Fin 2, σ j * x j ^ 2 := by
    rcases data.model_kind with hstd | hnest
    · rw [hstd] at hc ⊢
      exact Model.exists_standard_critical_coordinates q hc
    · rw [hnest] at hc ⊢
      exact Model.exists_nested_critical_coordinates q hc
  let h : S2 → Real := fun y => inner Real (M.v : E3)
    (data.toTerminalSaddleGeometry.filledModel y)
  have hfactor (x : E2) (hx : x ∈ C.source) :
      h (C x) = h q + (data.scale*σ 0)*(x 0)^2 + (data.scale*σ 1)*(x 1)^2 := by
    change inner Real (M.v : E3) (data.transport (data.model (C x))) =
      inner Real (M.v : E3) (data.transport (data.model q)) +
        (data.scale*σ 0)*(x 0)^2 + (data.scale*σ 1)*(x 1)^2
    rw [data.transport_height, data.transport_height, hform x hx]
    simp only [Fin.sum_univ_two]
    ring
  have hscale (j : Fin 2) : data.scale*σ j ≠ 0 :=
    mul_ne_zero data.scale_pos.ne' (by rcases hσ j with hs | hs <;> rw [hs] <;> norm_num)
  obtain ⟨Q, s, t, hs, ht, hQ0, hQz, hQU, hQ, hQi, hQform⟩ :=
    Model.exists_signed_square_coordinates_of_factors C.open_source hC0
      (contDiffOn_const (c := data.scale*σ 0))
      (contDiffOn_const (c := data.scale*σ 1)) (hscale 0) (hscale 1) hfactor
  let D := Q.trans C
  let τ : Fin 2 → Real := ![s, t]
  refine ⟨D, τ, ?_, ⟨hQ0, hQU hQ0⟩,
    by change C (Q 0) = q; rw [hQz, hCq], ?_, ?_, ?_⟩
  · intro j
    fin_cases j
    · exact hs
    · exact ht
  · exact hC.comp (hQ.contMDiffOn.mono inter_subset_left) (fun _ hx => hx.2)
  · exact hQi.contMDiffOn.comp (hCi.mono inter_subset_left) (fun _ hx => hx.2)
  · intro x hx
    change h (C (Q x)) = _
    rw [hQform x hx.1]
    simp only [τ, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring

theorem exists_terminal_model_extremum_coordinates
    (data : TerminalSaddleData M P p e) (i : Fin 3) :
    let h : S2 → Real := fun q => inner Real (M.v : E3)
      (data.toTerminalSaddleGeometry.filledModel q)
    ∃ q ∈ data.toTerminalSaddleGeometry.modelDomain i,
      mfderiv (𝓡 2) 𝓘(Real, Real) h q = 0 ∧
      ∃ C : OpenPartialHomeomorph E2 S2,
        0 ∈ C.source ∧ C 0 = q ∧
        ContMDiffOn (𝓡 2) (𝓡 2) ∞ C C.source ∧
        ContMDiffOn (𝓡 2) (𝓡 2) ∞ C.symm C.target ∧
        ((h q < data.ends.lowerCut ∧
            ∀ x ∈ C.source, h (C x) = h q + ‖x‖^2) ∨
          (data.ends.upperCut < h q ∧
            ∀ x ∈ C.source, h (C x) = h q - ‖x‖^2)) := by
  let h : S2 → Real := fun q => inner Real (M.v : E3)
    (data.toTerminalSaddleGeometry.filledModel q)
  obtain ⟨q, hqK, hqc, hcases⟩ := terminal_model_domain_extremum data i
  obtain ⟨C, σ, hσ, hC0, hCq, hC, hCi, hform⟩ :=
    exists_terminal_model_critical_coordinates data q hqc
  have hformH : ∀ x ∈ C.source, h (C x) = h q + ∑ j : Fin 2, σ j*x j^2 := hform
  refine ⟨q, hqK, hqc, C, hC0, hCq, hC, hCi, ?_⟩
  rcases hcases with ⟨hlo, hmin, _⟩ | ⟨hhi, hmax, _⟩
  · have hm : IsLocalMin h q := hmin
    have hsign := morse_signs_eq_one_of_isLocalMin (h := h) C hC0 σ hσ
      (by simpa only [hCq] using hformH) (by rw [hCq]; exact hm)
    refine Or.inl ⟨hlo, ?_⟩
    intro x hx
    simpa only [hsign, one_mul, ← EuclideanSpace.real_norm_sq_eq] using hformH x hx
  · have hformn (x : E2) (hx : x ∈ C.source) :
        (-h) (C x) = (-h) (C 0) + ∑ j : Fin 2, (-σ j)*x j^2 := by
      rw [hCq]
      change -h (C x) = -h q + _
      rw [hformH x hx]
      simp only [Fin.sum_univ_two]
      ring
    have hm : IsLocalMax h q := hmax
    have hsign := morse_signs_eq_one_of_isLocalMin (h := -h) C hC0 (fun j => -σ j)
      (fun j => by rcases hσ j with hs | hs <;> rw [hs] <;> simp) hformn
      (by rw [hCq]; exact hm.neg)
    have hsign' (j : Fin 2) : σ j = -1 := by have := hsign j; linarith
    refine Or.inr ⟨hhi, ?_⟩
    intro x hx
    simpa only [hsign', neg_one_mul, Finset.sum_neg_distrib,
      ← EuclideanSpace.real_norm_sq_eq, sub_eq_add_neg] using hformH x hx

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

end

end M38Schoenflies
