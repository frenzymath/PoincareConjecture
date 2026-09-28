import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.SelectedWallTransport

set_option autoImplicit false

open Set Function
open scoped ContDiff Manifold InnerProductSpace Matrix

namespace PoincareConjecture.M25.Topology3D

theorem exists_saddle_two_level_transport
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (u : UnitTwoSphere) (D : SaddlePieceData psi u)
    (R delta : ℝ) (N : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ))
    (hR : 0 < R) (hd : 0 < delta)
    (hdR : delta ≤ (5 * R / 8) ^ 2 / 128)
    (hmorse : {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 < (2 * R) ^ 2} ⊆ D.morse.target)
    (hcore : ∀ p : UnitTwoSphere,
      |⟪(u : E3), psi (p, 0)⟫_ℝ - ⟪(u : E3), psi (D.point, 0)⟫_ℝ| ≤
        3 * delta → p ∈ D.sourceCore)
    (hN : ∀ s : ℝ × ℝ, N (N s) = s ∧
      (N s).1 ^ 2 + (N s).2 ^ 2 = s.1 ^ 2 + s.2 ^ 2 ∧
      D.morseSign1 * (N s).1 ^ 2 + D.morseSign2 * (N s).2 ^ 2 =
        s.1 ^ 2 - s.2 ^ 2) :
    let j : UnitTwoSphere → E3 := fun p => psi (p, 0)
    let c := ⟪(u : E3), j D.point⟫_ℝ
    let r := 5 * R / 8
    let Dc := D.morse.symm '' {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 ≤ r ^ 2}
    let Do := D.morse.symm '' {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 < r ^ 2}
    let aa := Real.sqrt ((r ^ 2 - delta) / 2)
    let bb := Real.sqrt ((r ^ 2 + delta) / 2)
    let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
    let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
    let pm : Fin 4 → E3 := fun i => j (D.morse.symm (N (sx i * aa, sy i * bb)))
    let pp : Fin 4 → E3 := fun i => j (D.morse.symm (N (sx i * bb, sy i * aa)))
    let Lm := range j ∩ {y | ⟪(u : E3), y⟫_ℝ = c - delta}
    let Lp := range j ∩ {y | ⟪(u : E3), y⟫_ℝ = c + delta}
    ∃ F : E3 ≃ₜ E3,
      (∀ i, F (pm i) = pp i) ∧
      (∀ i, pm i ∈ j '' Dc) ∧
      Lp ∩ ((j '' Dc) \ (j '' Do)) = range pp ∧
      F '' (Lm \ (j '' Do)) = Lp \ (j '' Do) := by
  classical
  let j : UnitTwoSphere → E3 := fun p => psi (p, 0)
  let H := InnerProductSpace.toDual ℝ E3 (u : E3)
  let c := H (j D.point)
  let r := 5 * R / 8
  let Dc := D.morse.symm '' {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 ≤ r ^ 2}
  let Do := D.morse.symm '' {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 < r ^ 2}
  let aa := Real.sqrt ((r ^ 2 - delta) / 2)
  let bb := Real.sqrt ((r ^ 2 + delta) / 2)
  let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
  let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
  let pm : Fin 4 → UnitTwoSphere := fun i => D.morse.symm (N (sx i * aa, sy i * bb))
  let pp : Fin 4 → UnitTwoSphere := fun i => D.morse.symm (N (sx i * bb, sy i * aa))
  let qw : Fin 4 → ℝ → UnitTwoSphere := fun i t => D.morse.symm (N
    (sx i * Real.sqrt ((r ^ 2 + t) / 2), sy i * Real.sqrt ((r ^ 2 - t) / 2)))
  obtain ⟨V, K, L, hK, hL, hV, hcV, _support, _hcompact, _hsupport, _hsubset,
    _hjoint, _hjointInv, _hform, _hflowSupport, _hSphere, _hfixed, _hheight,
    _hDo, _hDc, _hclosure, _hqw, hwall, hport, hflow⟩ :=
    exists_saddle_selected_wall_transport psi hpsi u D R delta hR hd hdR
      hmorse hcore N hN
  let F := (boundedFlowDiffeomorph V hK hL hV hcV (2 * delta)).toHomeomorph
  have hji : Injective j := by
    intro p q hpq
    exact congrArg Prod.fst (hpsi.2.1
      ⟨mem_univ _, by norm_num⟩ ⟨mem_univ _, by norm_num⟩ hpq)
  have hminus : |(-delta)| ≤ 2 * delta := by rw [abs_neg, abs_of_pos hd]; linarith
  have hplus : |delta| ≤ 2 * delta := by rw [abs_of_pos hd]; linarith
  have hzero : |(0 : ℝ)| < 1 / 8 := by norm_num
  have hqwminus (i : Fin 4) : qw i (-delta) = pm i := by
    simp only [qw, pm, aa, bb, sub_neg_eq_add, ← sub_eq_add_neg]
  have hqwplus (i : Fin 4) : qw i delta = pp i := rfl
  have hwall' (t : ℝ) (ht : |t| ≤ 2 * delta) :
      {p : UnitTwoSphere | p ∈ Dc \ Do ∧ H (j p) = c + t} = range (fun i => qw i t) := by
    simpa only [qw, add_zero, one_pow, mul_one] using hwall t ht
  have hport' (i : Fin 4) : F (j (pm i)) = j (pp i) := by
    have hh := hport i 0 hzero (-delta) delta hminus hplus
    have htime : delta - -delta = 2 * delta := by ring
    simp only [htime, add_zero, one_pow, mul_one, sub_neg_eq_add,
      ← sub_eq_add_neg] at hh
    exact hh
  have hpm (i : Fin 4) : pm i ∈ Dc := by
    have hh : pm i ∈ {p : UnitTwoSphere | p ∈ Dc \ Do ∧ H (j p) = c + -delta} := by
      rw [hwall' (-delta) hminus]
      exact ⟨i, hqwminus i⟩
    exact hh.1.1
  have hwallAmbient :
      (range j ∩ {y | H y = c + delta}) ∩ ((j '' Dc) \ (j '' Do)) =
        range (fun i => j (pp i)) := by
    ext y
    constructor
    · rintro ⟨⟨⟨p, rfl⟩, hpheight⟩, ⟨q, hq, hqp⟩, hout⟩
      have hpDc : p ∈ Dc := hji hqp ▸ hq
      have hpDo : p ∉ Do := fun hp => hout ⟨p, hp, rfl⟩
      have hh : p ∈ {p : UnitTwoSphere | p ∈ Dc \ Do ∧ H (j p) = c + delta} :=
        ⟨⟨hpDc, hpDo⟩, hpheight⟩
      rw [hwall' delta hplus] at hh
      obtain ⟨i, hi⟩ := hh
      exact ⟨i, congrArg j ((hqwplus i).symm.trans hi)⟩
    · rintro ⟨i, rfl⟩
      have hh : pp i ∈ {p : UnitTwoSphere | p ∈ Dc \ Do ∧ H (j p) = c + delta} := by
        rw [hwall' delta hplus]
        exact ⟨i, hqwplus i⟩
      refine ⟨⟨mem_range_self _, hh.2⟩, ⟨_, hh.1.1, rfl⟩, ?_⟩
      rintro ⟨p, hp, hpi⟩
      exact hh.1.2 (hji hpi ▸ hp)
  refine ⟨F, hport', fun i => ⟨pm i, hpm i, rfl⟩, hwallAmbient, ?_⟩
  have hh := (hflow (-delta) delta hminus hplus).1
  have htime : delta - -delta = 2 * delta := by ring
  simp only [htime, ← sub_eq_add_neg] at hh
  exact hh

end PoincareConjecture.M25.Topology3D
