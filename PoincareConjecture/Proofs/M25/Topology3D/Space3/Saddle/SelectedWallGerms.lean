import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.PieceData
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.MorseRadialChart
import PoincareConjecture.Proofs.M25.Topology3D.Space3.HorizontalBandField
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Comp

set_option autoImplicit false
open Set Metric Function
open scoped ContDiff Manifold InnerProductSpace Topology
namespace PoincareConjecture.M25.Topology3D

set_option maxHeartbeats 3000000 in

set_option linter.unusedVariables false in

theorem exists_saddle_selected_wall_germs
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (u : UnitTwoSphere) (D : SaddlePieceData psi u)
    (W : SaddleLowerLevelData D)
    (R b epsilon : ℝ) (hR : 0 < R) (hb : 0 < b)
    (hepsilon : 0 < epsilon) (hepsilonb : epsilon ≤ b / 8)
    (P : OpenPartialHomeomorph (ℝ × ℝ) E2)
    (A : OpenPartialHomeomorph ((ℝ × ℝ) × ℝ) E3)
    (hPsource : P.source = {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 < (2 * R) ^ 2})
    (hPs : ContDiffOn ℝ ∞ P P.source)
    (hPi : ContDiffOn ℝ ∞ P.symm P.target)
    (hPmorse : P.source ⊆ D.morse.target)
    (hPform : ∀ s ∈ P.source, D.morse.symm s ∈ D.protectedSet ∧
      P s = horizontalBandProjection u (psi (D.morse.symm s, 0)))
    (hAsource : A.source =
      {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 < (2 * R) ^ 2} ×ˢ
        Ioo (⟪(u : E3), psi (D.point, 0)⟫_ℝ - 8 * b)
          (⟪(u : E3), psi (D.point, 0)⟫_ℝ + 8 * b))
    (hAform : ∀ w ∈ A.source,
      A w = (heightPlaneCoordinates u).symm (P w.1, w.2) ∧
      (A w ∈ range (fun q : UnitTwoSphere => psi (q, 0)) ↔
        w.2 = ⟪(u : E3), psi (D.point, 0)⟫_ℝ +
          D.morseSign1 * w.1.1 ^ 2 + D.morseSign2 * w.1.2 ^ 2)) :
    let j : UnitTwoSphere → E3 := fun q => psi (q, 0)
    let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
    let c := H (j D.point)
    let L := heightPlaneCoordinates u
    let pi := horizontalBandProjection u
    let S := range j
    let r2 : ℝ × ℝ → ℝ := fun s => s.1 ^ 2 + s.2 ^ 2
    let Q : ℝ × ℝ → ℝ := fun s =>
      D.morseSign1 * s.1 ^ 2 + D.morseSign2 * s.2 ^ 2
    let J2 : E2 ≃L[ℝ] (ℝ × ℝ) :=
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).trans
        (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)
    let rho : ℝ := 5 * R / 8
    let delta : ℝ := min (epsilon / 8)
      (min ((c - W.level) / 4) (rho ^ 2 / 128))
    let J : Set ℝ := Ioo (-(1 / 8)) (1 / 8)
    let T : Set ℝ := Ioo (-2 * delta) (2 * delta)
    let U : Set (ℝ × ℝ) := T ×ˢ J
    let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
    let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
    let xi : Fin 4 → (ℝ × ℝ) → (ℝ × ℝ) := fun i p =>
      (sx i * Real.sqrt ((rho ^ 2 * (1 + p.2) ^ 2 + p.1) / 2),
        sy i * Real.sqrt ((rho ^ 2 * (1 + p.2) ^ 2 - p.1) / 2))
    let port : Fin 4 → E2 := fun i =>
      J2.symm (sx i / Real.sqrt 2, sy i / Real.sqrt 2)
    ∃ (N : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ))
      (Bwall : BallNeighborhoodChart E2 E2)
      (E : Fin 4 → OpenPartialHomeomorph (ℝ × ℝ) UnitTwoSphere),
    let g : Fin 4 → (ℝ × ℝ) → E2 := fun i p => pi (j (E i p))
    let Vi : ℝ → Set E2 := fun r => P '' {s | r2 s < r ^ 2}
    let Kann : Set E2 := Bwall.chart ''
      {v : E2 | 7 / 8 < ‖v‖ ∧ ‖v‖ < 9 / 8}
    let Ei : Fin 4 → Set UnitTwoSphere := fun i =>
      {q | q ∈ D.morse.source ∧
        (7 * rho / 8) ^ 2 < r2 (D.morse q) ∧
        r2 (D.morse q) < (9 * rho / 8) ^ 2 ∧
        |Q (D.morse q)| < 2 * delta ∧
        0 < sx i * (N (D.morse q)).1 ∧
        0 < sy i * (N (D.morse q)).2}
    0 < delta ∧ 2 * delta < epsilon ∧ 2 * delta < 8 * b ∧
    W.level < c - delta ∧ 2 * delta ≤ rho ^ 2 / 64 ∧
    R / 2 < 7 * rho / 8 ∧ 9 * rho / 8 < 3 * R / 4 ∧
    (D.morseSign1 = 1 → ∀ s, N s = s) ∧
    (D.morseSign1 = -1 → ∀ s : ℝ × ℝ, N s = (s.2, s.1)) ∧
    (∀ s : ℝ × ℝ, N (N s) = s ∧ r2 (N s) = r2 s ∧
      Q (N s) = s.1 ^ 2 - s.2 ^ 2) ∧
    Bwall.chart.source = ball (0 : E2) (16 / 5) ∧
    Bwall.chart.target = P.target ∧
    (∀ v : E2, Bwall.chart v = P (N (rho • J2 v))) ∧
    (∀ x ∈ P.target, Bwall.chart.symm x =
      J2.symm (rho⁻¹ • N (P.symm x))) ∧
    closedBall (0 : E2) 2 ⊆ Bwall.chart.source ∧
    Bwall.inside = Vi rho ∧
    Bwall.closedRegion = P '' {s | r2 s ≤ rho ^ 2} ∧
    Bwall.boundary = P '' {s | r2 s = rho ^ 2} ∧
    (∀ i : Fin 4, ‖port i‖ = 1) ∧ Function.Injective port ∧
    (∀ i : Fin 4, (E i).source = U ∧ (E i).target = Ei i ∧
      ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ (E i) (E i).source ∧
      ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ (E i).symm (E i).target ∧
      (E i).target ⊆ D.protectedSet ∧
      (∀ p ∈ U, E i p = D.morse.symm (N (xi i p)) ∧
        g i p = P (N (xi i p)) ∧
        j (E i p) = L.symm (g i p, c + p.1) ∧
        rho ^ 2 / 4 < (rho ^ 2 * (1 + p.2) ^ 2 + p.1) / 2 ∧
        rho ^ 2 / 4 < (rho ^ 2 * (1 + p.2) ^ 2 - p.1) / 2 ∧
        g i p ∈ Vi (3 * R / 4) ∧
        g i p ∉ P '' {s | r2 s ≤ (R / 2) ^ 2}) ∧
      (∀ q ∈ (E i).target, (E i).symm q =
        (H (j q) - c, Real.sqrt (r2 (D.morse q)) / rho - 1)) ∧
      ContDiffOn ℝ ∞ (g i) U ∧
      (∀ t ∈ T, Set.InjOn (fun a => g i (t, a)) J ∧
        ∀ a ∈ J, deriv (fun a' => g i (t, a')) a ≠ 0) ∧
      (∀ a ∈ J, g i (0, a) = Bwall.chart ((1 + a) • port i)) ∧
      (∀ p ∈ U,
        (g i p ∈ Bwall.inside ↔ p.2 < 0) ∧
        (g i p ∈ Bwall.boundary ↔ p.2 = 0) ∧
        (g i p ∈ Bwall.closedRegion ↔ p.2 ≤ 0))) ∧
    (∀ i k : Fin 4, i ≠ k → Disjoint (E i).target (E k).target) ∧
    (⋃ i : Fin 4, (E i).target) =
      {q | q ∈ D.morse.source ∧
        (7 * rho / 8) ^ 2 < r2 (D.morse q) ∧
        r2 (D.morse q) < (9 * rho / 8) ^ 2 ∧
        |Q (D.morse q)| < 2 * delta} ∧
    (∀ t ∈ T,
      {x : E2 | x ∈ Kann ∧ L.symm (x, c + t) ∈ S} =
        ⋃ i : Fin 4, (fun a => g i (t, a)) '' J) ∧
    (∀ t ∈ T,
      {x : E2 | x ∈ Bwall.boundary ∧ L.symm (x, c + t) ∈ S} =
        range (fun i : Fin 4 => g i (t, 0))) ∧
    (∀ t ∈ T, Function.Injective (fun i : Fin 4 => g i (t, 0))) ∧
    {x : E2 | x ∈ Bwall.closedRegion ∧ L.symm (x, c) ∈ S} =
      Bwall.chart '' {v : E2 | ‖v‖ ≤ 1 ∧ (J2 v).1 ^ 2 = (J2 v).2 ^ 2} := by
  classical
  let j : UnitTwoSphere → E3 := fun q => psi (q, 0)
  let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
  let c := H (j D.point)
  let L := heightPlaneCoordinates u
  let pi := horizontalBandProjection u
  let S := range j
  let r2 : ℝ × ℝ → ℝ := fun s => s.1 ^ 2 + s.2 ^ 2
  let Q : ℝ × ℝ → ℝ := fun s => D.morseSign1 * s.1 ^ 2 + D.morseSign2 * s.2 ^ 2
  let J2 : E2 ≃L[ℝ] (ℝ × ℝ) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).trans
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)
  let rho : ℝ := 5 * R / 8
  let delta := min (epsilon / 8) (min ((c - W.level) / 4) (rho ^ 2 / 128))
  let J : Set ℝ := Ioo (-(1 / 8)) (1 / 8)
  let T : Set ℝ := Ioo (-2 * delta) (2 * delta)
  let U := T ×ˢ J
  let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
  let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
  let xi : Fin 4 → (ℝ × ℝ) → (ℝ × ℝ) := fun i p =>
    (sx i * Real.sqrt ((rho ^ 2 * (1 + p.2) ^ 2 + p.1) / 2),
      sy i * Real.sqrt ((rho ^ 2 * (1 + p.2) ^ 2 - p.1) / 2))
  let port : Fin 4 → E2 := fun i => J2.symm (sx i / Real.sqrt 2, sy i / Real.sqrt 2)
  have hrho : 0 < rho := by dsimp [rho]; positivity
  have hrho2 : 0 < rho ^ 2 := sq_pos_of_pos hrho
  have hgap : 0 < c - W.level := sub_pos.mpr W.level_lt_critical
  have hd : 0 < delta := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hde : delta ≤ epsilon / 8 := min_le_left _ _
  have hdw : delta ≤ (c - W.level) / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hdr : delta ≤ rho ^ 2 / 128 := (min_le_right _ _).trans (min_le_right _ _)
  have hdE : 2 * delta < epsilon := by linarith
  have hdB : 2 * delta < 8 * b := by linarith
  have hdW : W.level < c - delta := by linarith
  have hdR : 2 * delta ≤ rho ^ 2 / 64 := by linarith
  have hTabs (t : ℝ) (ht : t ∈ T) : |t| < 2 * delta :=
    abs_lt.mpr ⟨by linarith [ht.1], ht.2⟩
  have hmargin : R / 2 < 7 * rho / 8 ∧ 9 * rho / 8 < 3 * R / 4 := by
    dsimp [rho]; constructor <;> linarith
  have hJ2 (v : E2) : ‖v‖ ^ 2 = r2 (J2 v) := by
    change ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2
    simpa only [Fin.sum_univ_two] using EuclideanSpace.real_norm_sq_eq v
  have hsign : D.morseSign1 = 1 ∨ D.morseSign1 = -1 := mul_self_eq_one_iff.mp D.morseSign1_sq
  let N : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) := if D.morseSign1 = 1 then
    ContinuousLinearEquiv.refl ℝ (ℝ × ℝ) else ContinuousLinearEquiv.prodComm ℝ ℝ ℝ
  have hN1 (h : D.morseSign1 = 1) (s : ℝ × ℝ) : N s = s := by simp [N, h]
  have hNneg (h : D.morseSign1 = -1) (s : ℝ × ℝ) : N s = (s.2, s.1) := by
    norm_num [N, h]
    rfl
  have hN (s : ℝ × ℝ) : N (N s) = s ∧ r2 (N s) = r2 s ∧
      Q (N s) = s.1 ^ 2 - s.2 ^ 2 := by
    rcases hsign with h | h <;>
      norm_num [N, h, r2, Q, D.morseSigns_opposite, add_comm] <;> ring
  have hQN (s : ℝ × ℝ) : Q s = (N s).1 ^ 2 - (N s).2 ^ 2 := by
    simpa only [(hN s).1] using (hN (N s)).2.2
  have hsg (i : Fin 4) : (sx i) ^ 2 = 1 ∧ (sy i) ^ 2 = 1 := by
    fin_cases i <;> norm_num [sx, sy]
  let M : E2 ≃L[ℝ] (ℝ × ℝ) := {
    toFun := fun v => N (rho • J2 v)
    invFun := fun s => J2.symm (rho⁻¹ • N s)
    map_add' := by intros; simp [map_add, smul_add]
    map_smul' := by intros; simp [map_smul, smul_smul, mul_comm]
    left_inv := by
      intro v
      change J2.symm (rho⁻¹ • N (N (rho • J2 v))) = v
      rw [(hN _).1, inv_smul_smul₀ hrho.ne', J2.symm_apply_apply]
    right_inv := by
      intro s
      change N (rho • J2 (J2.symm (rho⁻¹ • N s))) = s
      rw [J2.apply_symm_apply, smul_inv_smul₀ hrho.ne', (hN s).1]
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  have hMr (v : E2) : r2 (M v) = rho ^ 2 * ‖v‖ ^ 2 := by
    change r2 (N (rho • J2 v)) = _
    rw [(hN _).2.1, hJ2]; dsimp [r2]; ring
  have hMQ (v : E2) : Q (M v) = rho ^ 2 * ((J2 v).1 ^ 2 - (J2 v).2 ^ 2) := by
    change Q (N (rho • J2 v)) = _
    rw [(hN _).2.2]; simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  have hMcmp (v : E2) (r : ℝ) (hr : 0 ≤ r) :
      (r2 (M v) < (rho * r) ^ 2 ↔ ‖v‖ < r) ∧
      (r2 (M v) = (rho * r) ^ 2 ↔ ‖v‖ = r) ∧
      (r2 (M v) ≤ (rho * r) ^ 2 ↔ ‖v‖ ≤ r) := by
    rw [hMr, mul_pow]
    exact ⟨(mul_lt_mul_iff_right₀ hrho2).trans (sq_lt_sq₀ (norm_nonneg v) hr),
      (mul_right_inj' hrho2.ne').trans (sq_eq_sq₀ (norm_nonneg v) hr),
      (mul_le_mul_iff_right₀ hrho2).trans (sq_le_sq₀ (norm_nonneg v) hr)⟩
  let Bchart := M.toHomeomorph.toOpenPartialHomeomorph.trans P
  have hBsource : Bchart.source = ball (0 : E2) (16 / 5) := by
    ext v
    change (v ∈ univ ∧ M v ∈ P.source) ↔ v ∈ ball 0 (16 / 5)
    simp only [mem_univ, true_and, hPsource, mem_ofPred_eq, mem_ball_zero_iff]
    have hscale : (2 * R) ^ 2 = (rho * (16 / 5)) ^ 2 := by dsimp [rho]; ring
    rw [hscale]; exact (hMcmp v (16 / 5) (by norm_num)).1
  have hBtarget : Bchart.target = P.target := by ext x; simp [Bchart]
  have hBbuffer : closedBall (0 : E2) 2 ⊆ Bchart.source := by
    rw [hBsource]; intro v hv; exact mem_ball_zero_iff.mpr (by
      have := mem_closedBall_zero_iff.mp hv; linarith)
  let Bwall : BallNeighborhoodChart E2 E2 := {
    chart := Bchart
    closedBall_subset_source :=
      (closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2)).trans hBbuffer
    smooth := hPs.comp M.contDiff.contDiffOn (fun _ hp => hp.2)
    smooth_symm := M.symm.contDiff.comp_contDiffOn (hPi.mono inter_subset_left) }
  let Vi : ℝ → Set E2 := fun r => P '' {s | r2 s < r ^ 2}
  let Kann : Set E2 := Bwall.chart '' {v : E2 | 7 / 8 < ‖v‖ ∧ ‖v‖ < 9 / 8}
  have hMi (s : Set E2) (t : Set (ℝ × ℝ)) (hst : ∀ v, v ∈ s ↔ M v ∈ t) : M '' s = t := by
    ext y; constructor
    · rintro ⟨v, hv, rfl⟩; exact (hst v).mp hv
    · intro hy; exact ⟨M.symm y, (hst _).mpr (by simpa using hy), M.apply_symm_apply y⟩
  have hBinside : Bwall.inside = Vi rho := by
    change (P ∘ M) '' ball 0 1 = _
    rw [image_comp, hMi (ball 0 1) {s | r2 s < rho ^ 2} (fun v => by
      simpa only [mem_ball_zero_iff, mem_ofPred_eq, mul_one] using (hMcmp v 1 zero_le_one).1.symm)]
  have hBclosed : Bwall.closedRegion = P '' {s | r2 s ≤ rho ^ 2} := by
    change (P ∘ M) '' closedBall 0 1 = _
    rw [image_comp, hMi (closedBall 0 1) {s | r2 s ≤ rho ^ 2} (fun v => by
      simpa only [mem_closedBall_zero_iff, mem_ofPred_eq, mul_one] using
        (hMcmp v 1 zero_le_one).2.2.symm)]
  have hBboundary : Bwall.boundary = P '' {s | r2 s = rho ^ 2} := by
    change (P ∘ M) '' sphere 0 1 = _
    rw [image_comp, hMi (sphere 0 1) {s | r2 s = rho ^ 2} (fun v => by
      simpa only [mem_sphere_zero_iff_norm, mem_ofPred_eq, mul_one] using
        (hMcmp v 1 zero_le_one).2.1.symm)]
  have hMann (v : E2) : (7 / 8 < ‖v‖ ∧ ‖v‖ < 9 / 8) ↔
      (7 * rho / 8) ^ 2 < r2 (M v) ∧ r2 (M v) < (9 * rho / 8) ^ 2 := by
    have hl := not_congr (hMcmp v (7 / 8) (by norm_num)).2.2
    have hu := (hMcmp v (9 / 8) (by norm_num)).1
    simp only [not_le] at hl
    simpa only [show rho * (7 / 8) = 7 * rho / 8 by ring,
      show rho * (9 / 8) = 9 * rho / 8 by ring] using and_congr hl.symm hu.symm
  have hport (i : Fin 4) : ‖port i‖ = 1 := by
    have hh := hJ2 (port i)
    change ‖port i‖ ^ 2 = (sx i / Real.sqrt 2) ^ 2 + (sy i / Real.sqrt 2) ^ 2 at hh
    rw [div_pow, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), (hsg i).1, (hsg i).2] at hh
    nlinarith [norm_nonneg (port i)]
  have hportI : Injective port := by
    intro i k hik
    have hh := congrArg J2 hik
    have hx := congrArg (fun p : ℝ × ℝ => p.1 * Real.sqrt 2) hh
    have hy := congrArg (fun p : ℝ × ℝ => p.2 * Real.sqrt 2) hh
    simp only [port, J2.apply_symm_apply,
      div_mul_cancel₀ _ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'] at hx hy
    fin_cases i <;> fin_cases k <;> norm_num [sx] at hx <;> norm_num [sy] at hy <;> rfl
  have hrad (p : ℝ × ℝ) (hp : p ∈ U) :
      (7 * rho / 8) ^ 2 < rho ^ 2 * (1 + p.2) ^ 2 ∧
      rho ^ 2 * (1 + p.2) ^ 2 < (9 * rho / 8) ^ 2 := by
    have hlo := mul_lt_mul_of_pos_left
      ((sq_lt_sq₀ (by norm_num : (0 : ℝ) ≤ 7 / 8) (by linarith [hp.2.1])).mpr
        (by linarith [hp.2.1] : (7 : ℝ) / 8 < 1 + p.2)) hrho2
    have hhi := mul_lt_mul_of_pos_left
      ((sq_lt_sq₀ (by linarith [hp.2.1]) (by norm_num : (0 : ℝ) ≤ 9 / 8)).mpr
        (by linarith [hp.2.2] : 1 + p.2 < (9 : ℝ) / 8)) hrho2
    constructor <;> nlinarith
  have hroots (p : ℝ × ℝ) (hp : p ∈ U) :
      rho ^ 2 / 4 < (rho ^ 2 * (1 + p.2) ^ 2 + p.1) / 2 ∧
      rho ^ 2 / 4 < (rho ^ 2 * (1 + p.2) ^ 2 - p.1) / 2 := by
    have ht := hp.1; have hh := hrad p hp; constructor <;> nlinarith [ht.1, ht.2, hh.1]
  let Y : Fin 4 → (ℝ × ℝ) → (ℝ × ℝ) := fun i p => N (xi i p)
  let back : (ℝ × ℝ) → (ℝ × ℝ) := fun s => (Q s, Real.sqrt (r2 s) / rho - 1)
  let Z : Fin 4 → Set (ℝ × ℝ) := fun i => {s |
    (7 * rho / 8) ^ 2 < r2 s ∧ r2 s < (9 * rho / 8) ^ 2 ∧ |Q s| < 2 * delta ∧
      0 < sx i * (N s).1 ∧ 0 < sy i * (N s).2}
  have hY (i : Fin 4) (p : ℝ × ℝ) (hp : p ∈ U) :
      r2 (Y i p) = rho ^ 2 * (1 + p.2) ^ 2 ∧ Q (Y i p) = p.1 ∧
      0 < sx i * (N (Y i p)).1 ∧ 0 < sy i * (N (Y i p)).2 := by
    have hp1 : 0 < (rho ^ 2 * (1 + p.2) ^ 2 + p.1) / 2 := by linarith [(hroots p hp).1]
    have hp2 : 0 < (rho ^ 2 * (1 + p.2) ^ 2 - p.1) / 2 := by linarith [(hroots p hp).2]
    have hsq1 := Real.sq_sqrt hp1.le; have hsq2 := Real.sq_sqrt hp2.le
    refine ⟨?_, ?_, ?_, ?_⟩
    · change r2 (N (xi i p)) = _
      rw [(hN _).2.1]; dsimp [r2, xi]
      rw [mul_pow, mul_pow, (hsg i).1, (hsg i).2]; nlinarith
    · change Q (N (xi i p)) = _
      rw [(hN _).2.2]; dsimp [xi]
      rw [mul_pow, mul_pow, (hsg i).1, (hsg i).2]; nlinarith
    · change 0 < sx i * (N (N (xi i p))).1
      rw [(hN _).1]; dsimp [xi]
      simpa only [← mul_assoc, ← pow_two, (hsg i).1, one_mul] using Real.sqrt_pos.mpr hp1
    · change 0 < sy i * (N (N (xi i p))).2
      rw [(hN _).1]; dsimp [xi]
      simpa only [← mul_assoc, ← pow_two, (hsg i).2, one_mul] using Real.sqrt_pos.mpr hp2
  have hYZ (i : Fin 4) (p : ℝ × ℝ) (hp : p ∈ U) : Y i p ∈ Z i := by
    obtain ⟨hr, hq, hx, hy⟩ := hY i p hp
    exact ⟨by rw [hr]; exact (hrad p hp).1, by rw [hr]; exact (hrad p hp).2,
      by rw [hq]; exact hTabs _ hp.1, hx, hy⟩
  have hYP (i : Fin 4) (p : ℝ × ℝ) (hp : p ∈ U) : Y i p ∈ P.source := by
    rw [hPsource]; change r2 (Y i p) < (2 * R) ^ 2
    have hh := (hYZ i p hp).2.1; dsimp [rho] at hh; nlinarith [sq_pos_of_pos hR]
  have hZP (i : Fin 4) (s : ℝ × ℝ) (hs : s ∈ Z i) : s ∈ P.source := by
    rw [hPsource]; change r2 s < (2 * R) ^ 2
    have hh := hs.2.1; dsimp [rho] at hh; nlinarith [sq_pos_of_pos hR]
  have hleft (i : Fin 4) (p : ℝ × ℝ) (hp : p ∈ U) : back (Y i p) = p := by
    apply Prod.ext
    · exact (hY i p hp).2.1
    · change Real.sqrt (r2 (Y i p)) / rho - 1 = p.2
      have ht : 0 ≤ rho * (1 + p.2) := mul_nonneg hrho.le (by linarith [hp.2.1])
      rw [(hY i p hp).1, show rho ^ 2 * (1 + p.2) ^ 2 = (rho * (1 + p.2)) ^ 2 by ring,
        Real.sqrt_sq ht]
      field_simp [hrho.ne']; ring
  have hsigned (e x : ℝ) (he : e ^ 2 = 1) (hx : 0 < e * x) :
      e * Real.sqrt (x ^ 2) = x := by
    rcases sq_eq_one_iff.mp he with rfl | rfl
    · simp only [one_mul] at hx ⊢; exact Real.sqrt_sq hx.le
    · have hn : x < 0 := by linarith
      rw [Real.sqrt_sq_eq_abs, abs_of_neg hn]; ring
  have hright (i : Fin 4) (s : ℝ × ℝ) (hs : s ∈ Z i) : back s ∈ U ∧ Y i (back s) = s := by
    have hspos : 0 < r2 s := lt_trans (by positivity) hs.1
    have hk := Real.sqrt_nonneg (r2 s); have hk2 := Real.sq_sqrt hspos.le
    have hkl : 7 * rho / 8 < Real.sqrt (r2 s) := by nlinarith [hs.1]
    have hku : Real.sqrt (r2 s) < 9 * rho / 8 := by nlinarith [hs.2.1]
    have hbs : back s ∈ U := ⟨by
      change -2 * delta < Q s ∧ Q s < 2 * delta
      simpa only [neg_mul] using abs_lt.mp hs.2.2.1, ⟨by
      change -(1 / 8) < Real.sqrt (r2 s) / rho - 1
      have := (lt_div_iff₀ hrho).mpr (show (7 / 8) * rho < Real.sqrt (r2 s) by linarith)
      linarith, by
      change Real.sqrt (r2 s) / rho - 1 < 1 / 8
      have := (div_lt_iff₀ hrho).mpr (show Real.sqrt (r2 s) < (9 / 8) * rho by linarith)
      linarith⟩⟩
    have hbr : rho ^ 2 * (1 + (back s).2) ^ 2 = r2 s := by
      calc
        _ = Real.sqrt (r2 s) ^ 2 := by dsimp [back]; field_simp [hrho.ne']; ring
        _ = r2 s := hk2
    have hnr : (N s).1 ^ 2 + (N s).2 ^ 2 = r2 s := (hN s).2.1
    have hq := hQN s
    refine ⟨hbs, N.injective ?_⟩
    change N (N (xi i (back s))) = N s
    rw [(hN _).1]; apply Prod.ext
    · change sx i * Real.sqrt ((rho ^ 2 * (1 + (back s).2) ^ 2 + Q s) / 2) = (N s).1
      rw [show (rho ^ 2 * (1 + (back s).2) ^ 2 + Q s) / 2 = (N s).1 ^ 2 by nlinarith]
      exact hsigned _ _ (hsg i).1 hs.2.2.2.1
    · change sy i * Real.sqrt ((rho ^ 2 * (1 + (back s).2) ^ 2 - Q s) / 2) = (N s).2
      rw [show (rho ^ 2 * (1 + (back s).2) ^ 2 - Q s) / 2 = (N s).2 ^ 2 by nlinarith]
      exact hsigned _ _ (hsg i).2 hs.2.2.2.2
  have hrs : ContDiff ℝ ∞ r2 := by dsimp [r2]; fun_prop
  have hQs : ContDiff ℝ ∞ Q := by dsimp [Q]; fun_prop
  have hYs (i : Fin 4) : ContDiffOn ℝ ∞ (Y i) U := by
    apply N.contDiff.comp_contDiffOn
    exact (contDiffOn_const.mul
      ((by fun_prop : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ =>
        (rho ^ 2 * (1 + p.2) ^ 2 + p.1) / 2) U).sqrt (fun p hp =>
          (lt_trans (by positivity) (hroots p hp).1).ne'))).prodMk
      (contDiffOn_const.mul
        ((by fun_prop : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ =>
          (rho ^ 2 * (1 + p.2) ^ 2 - p.1) / 2) U).sqrt (fun p hp =>
            (lt_trans (by positivity) (hroots p hp).2).ne')))
  have hbs : ContDiffOn ℝ ∞ back {s | 0 < r2 s} :=
    hQs.contDiffOn.prodMk
      (((hrs.contDiffOn.sqrt (fun _ hs => hs.ne')).div_const rho).sub contDiffOn_const)
  have hZo (i : Fin 4) : IsOpen (Z i) := by
    change IsOpen ({s | (7 * rho / 8) ^ 2 < r2 s} ∩ ({s | r2 s < (9 * rho / 8) ^ 2} ∩
      ({s | |Q s| < 2 * delta} ∩ ({s | 0 < sx i * (N s).1} ∩ {s | 0 < sy i * (N s).2}))))
    exact (isOpen_lt continuous_const hrs.continuous).inter
      ((morseRadialDisc_geometry (9 * rho / 8) (by positivity)).1.inter
        ((isOpen_lt hQs.continuous.abs continuous_const).inter
          ((isOpen_lt continuous_const (by fun_prop)).inter
            (isOpen_lt continuous_const (by fun_prop)))))
  let X : Fin 4 → OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ) := fun i => {
    toFun := Y i, invFun := back, source := U, target := Z i
    map_source' := hYZ i, map_target' := fun s hs => (hright i s hs).1
    left_inv' := hleft i, right_inv' := fun s hs => (hright i s hs).2
    open_source := isOpen_Ioo.prod isOpen_Ioo, open_target := hZo i
    continuousOn_toFun := (hYs i).continuousOn
    continuousOn_invFun := hbs.continuousOn.mono (fun s hs => lt_trans (by positivity) hs.1) }
  let E : Fin 4 → OpenPartialHomeomorph (ℝ × ℝ) UnitTwoSphere := fun i => (X i).trans D.morse.symm
  let Ei : Fin 4 → Set UnitTwoSphere := fun i => {q | q ∈ D.morse.source ∧ D.morse q ∈ Z i}
  let g : Fin 4 → (ℝ × ℝ) → E2 := fun i p => pi (j (E i p))
  have hEs (i : Fin 4) : (E i).source = U := by
    ext p; change (p ∈ U ∧ Y i p ∈ D.morse.target) ↔ p ∈ U
    exact ⟨And.left, fun hp => ⟨hp, hPmorse (hYP i p hp)⟩⟩
  have hEt (i : Fin 4) : (E i).target = Ei i := rfl
  have hEm (i : Fin 4) : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ (E i) (E i).source :=
    D.morse_inverse.comp ((hYs i).contMDiffOn.mono inter_subset_left) (fun _ hp => hp.2)
  have hEi (i : Fin 4) : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ (E i).symm (E i).target :=
    hbs.contMDiffOn.comp (D.morse_smooth.mono inter_subset_left)
      (fun q hq => lt_trans (by positivity) hq.2.1)
  have hprotected (i : Fin 4) : (E i).target ⊆ D.protectedSet := by
    intro q hq; have hh := (hPform _ (hZP i _ hq.2)).1
    change D.morse.symm (D.morse q) ∈ D.protectedSet at hh
    rwa [D.morse.left_inv hq.1] at hh
  have hg (i : Fin 4) (p : ℝ × ℝ) (hp : p ∈ U) : g i p = P (Y i p) := (hPform _ (hYP i p hp)).2.symm
  have hgH (i : Fin 4) (p : ℝ × ℝ) (hp : p ∈ U) : H (j (E i p)) = c + p.1 := by
    have hh := D.morse_height (E i p) (D.morse.symm.map_source (hPmorse (hYP i p hp)))
    change H (j (E i p)) = c + D.morseSign1 * (D.morse (D.morse.symm (Y i p))).1 ^ 2 +
      D.morseSign2 * (D.morse (D.morse.symm (Y i p))).2 ^ 2 at hh
    rw [D.morse.right_inv (hPmorse (hYP i p hp))] at hh
    have hq := (hY i p hp).2.1; dsimp [Q] at hq; linarith
  have hgrec (i : Fin 4) (p : ℝ × ℝ) (hp : p ∈ U) : j (E i p) = L.symm (g i p, c + p.1) :=
    (heightPlaneCoordinates_reconstruct u _ (c + p.1) (hgH i p hp)).symm
  have hgs (i : Fin 4) : ContDiffOn ℝ ∞ (g i) U :=
    (hPs.comp (hYs i) (hYP i)).congr (hg i)
  have hgback (i : Fin 4) (p : ℝ × ℝ) (hp : p ∈ U) : back (P.symm (g i p)) = p := by
    rw [hg i p hp, P.left_inv (hYP i p hp)]; exact hleft i p hp
  have hgI (i : Fin 4) : InjOn (g i) U := by
    intro p hp q hq heq
    have hh := congrArg (fun x => back (P.symm x)) heq
    rwa [hgback i p hp, hgback i q hq] at hh
  have hZd (i k : Fin 4) (hik : i ≠ k) : Disjoint (Z i) (Z k) := by
    apply disjoint_left.mpr; intro s hs hk
    have hix := hs.2.2.2.1; have hiy := hs.2.2.2.2
    have hkx := hk.2.2.2.1; have hky := hk.2.2.2.2
    fin_cases i <;> fin_cases k <;> norm_num at hik <;>
      norm_num [sx, sy] at hix hiy hkx hky <;> linarith
  have hZcover (s : ℝ × ℝ) (hl : (7 * rho / 8) ^ 2 < r2 s)
      (hu : r2 s < (9 * rho / 8) ^ 2) (ht : |Q s| < 2 * delta) : ∃ i, s ∈ Z i := by
    have hn : (N s).1 ^ 2 + (N s).2 ^ 2 = r2 s := (hN s).2.1
    have hq := hQN s; obtain ⟨htl, htu⟩ := abs_lt.mp ht
    have hx2 : 0 < (N s).1 ^ 2 := by nlinarith
    have hy2 : 0 < (N s).2 ^ 2 := by nlinarith
    by_cases hx : 0 < (N s).1 <;> by_cases hy : 0 < (N s).2
    · exact ⟨0, hl, hu, ht, by simpa [sx] using hx, by simpa [sy] using hy⟩
    · refine ⟨3, hl, hu, ht, ?_, ?_⟩
      · change 0 < 1 * (N s).1
        simpa only [one_mul] using hx
      change 0 < -1 * (N s).2
      nlinarith only [hy, hy2]
    · refine ⟨1, hl, hu, ht, ?_, ?_⟩
      · change 0 < -1 * (N s).1
        nlinarith only [hx, hx2]
      · change 0 < 1 * (N s).2
        simpa only [one_mul] using hy
    · refine ⟨2, hl, hu, ht, ?_, ?_⟩
      · change 0 < -1 * (N s).1
        nlinarith only [hx, hx2]
      · change 0 < -1 * (N s).2
        nlinarith only [hy, hy2]
  have hPsmall (s : ℝ × ℝ) (hs : r2 s ≤ (3 * R / 4) ^ 2) : s ∈ P.source := by
    rw [hPsource]; change r2 s < (2 * R) ^ 2; nlinarith [sq_pos_of_pos hR]
  have hPimage (s : ℝ × ℝ) (hs : s ∈ P.source) (V : Set (ℝ × ℝ)) (hV : V ⊆ P.source) :
      P s ∈ P '' V ↔ s ∈ V := by
    constructor
    · rintro ⟨y, hy, heq⟩; exact (P.injOn (hV hy) hs heq) ▸ hy
    · exact mem_image_of_mem P
  have hbuffer (i : Fin 4) (p : ℝ × ℝ) (hp : p ∈ U) :
      g i p ∈ Vi (3 * R / 4) ∧ g i p ∉ P '' {s | r2 s ≤ (R / 2) ^ 2} := by
    have hh := hYZ i p hp
    rw [hg i p hp]
    refine ⟨⟨Y i p, ?_, rfl⟩, ?_⟩
    · change r2 (Y i p) < (3 * R / 4) ^ 2
      have := hh.2.1; dsimp [rho] at this; nlinarith [sq_pos_of_pos hR]
    · rw [hPimage _ (hYP i p hp) {s | r2 s ≤ (R / 2) ^ 2}
        (fun s hs => hPsmall s (by
          change r2 s ≤ (R / 2) ^ 2 at hs
          nlinarith [sq_nonneg R]))]
      have := hh.1
      dsimp [rho] at this
      intro hs
      change r2 (Y i p) ≤ (R / 2) ^ 2 at hs
      nlinarith [sq_pos_of_pos hR]
  have hgtests (i : Fin 4) (p : ℝ × ℝ) (hp : p ∈ U) :
      (g i p ∈ Bwall.inside ↔ p.2 < 0) ∧ (g i p ∈ Bwall.boundary ↔ p.2 = 0) ∧
      (g i p ∈ Bwall.closedRegion ↔ p.2 ≤ 0) := by
    have hpc : {s | r2 s ≤ rho ^ 2} ⊆ P.source := fun s hs => hPsmall s (by
      change r2 s ≤ rho ^ 2 at hs
      dsimp [rho] at hs; nlinarith [sq_nonneg R])
    rw [hg i p hp, hBinside, hBboundary, hBclosed]
    change (P (Y i p) ∈ P '' {s | r2 s < rho ^ 2} ↔ _) ∧ _
    rw [hPimage _ (hYP i p hp) {s | r2 s < rho ^ 2}
        (fun s hs => hpc (show r2 s ≤ rho ^ 2 from (show r2 s < rho ^ 2 from hs).le)),
      hPimage _ (hYP i p hp) {s | r2 s = rho ^ 2}
        (fun s hs => hpc (show r2 s ≤ rho ^ 2 from (show r2 s = rho ^ 2 from hs).le)),
      hPimage _ (hYP i p hp) {s | r2 s ≤ rho ^ 2} hpc]
    simp only [mem_ofPred_eq, (hY i p hp).1]
    have ha : 0 ≤ 1 + p.2 := by linarith [hp.2.1]
    have hl := (mul_lt_mul_iff_right₀ hrho2 : rho ^ 2 * (1 + p.2) ^ 2 < rho ^ 2 * 1 ^ 2 ↔ _)
    have he := (mul_right_inj' hrho2.ne' : rho ^ 2 * (1 + p.2) ^ 2 = rho ^ 2 * 1 ^ 2 ↔ _)
    have hu := (mul_le_mul_iff_right₀ hrho2 : rho ^ 2 * (1 + p.2) ^ 2 ≤ rho ^ 2 * 1 ^ 2 ↔ _)
    simp only [one_pow, mul_one] at hl he hu
    have hsqL : (1 + p.2) ^ 2 < 1 ↔ 1 + p.2 < 1 := by
      simpa only [one_pow] using sq_lt_sq₀ ha zero_le_one
    have hsqE : (1 + p.2) ^ 2 = 1 ↔ 1 + p.2 = 1 := by
      simpa only [one_pow] using sq_eq_sq₀ ha zero_le_one
    have hsqU : (1 + p.2) ^ 2 ≤ 1 ↔ 1 + p.2 ≤ 1 := by
      simpa only [one_pow] using sq_le_sq₀ ha zero_le_one
    exact ⟨(hl.trans hsqL).trans (by constructor <;> intro h <;> linarith),
      (he.trans hsqE).trans (by constructor <;> intro h <;> linarith),
      (hu.trans hsqU).trans (by constructor <;> intro h <;> linarith)⟩
  have hradial (i : Fin 4) (t : ℝ) (ht : t ∈ T) : InjOn (fun a => g i (t, a)) J ∧
      ∀ a ∈ J, deriv (fun a' => g i (t, a')) a ≠ 0 := by
    refine ⟨fun a ha b hb heq => congrArg Prod.snd (hgI i ⟨ht, ha⟩ ⟨ht, hb⟩ heq), ?_⟩
    intro a ha hzero
    let f : E2 → ℝ := fun x => (back (P.symm x)).2
    have hp := hYP i (t, a) ⟨ht, ha⟩
    have hpi : P.symm (g i (t, a)) = Y i (t, a) := by rw [hg i _ ⟨ht, ha⟩, P.left_inv hp]
    have hpos : 0 < r2 (P.symm (g i (t, a))) := by
      rw [hpi]
      exact lt_trans (by positivity) (hYZ i _ ⟨ht, ha⟩).1
    have hpt : g i (t, a) ∈ P.target := by rw [hg i _ ⟨ht, ha⟩]; exact P.map_source hp
    have hf : ContDiffAt ℝ ∞ f (g i (t, a)) :=
      ((hbs.contDiffAt ((isOpen_lt continuous_const hrs.continuous).mem_nhds hpos)).comp _
        (hPi.contDiffAt (P.open_target.mem_nhds hpt))).snd
    have hga : ContDiffAt ℝ ∞ (fun a' => g i (t, a')) a :=
      ((hgs i).contDiffAt ((isOpen_Ioo.prod isOpen_Ioo).mem_nhds ⟨ht, ha⟩)).comp a
        (contDiffAt_const.prodMk contDiffAt_id)
    have hJa : J ∈ 𝓝 a := isOpen_Ioo.mem_nhds ha
    have hevent : (fun a' => f (g i (t, a'))) =ᶠ[𝓝 a] id := by
      filter_upwards [hJa] with a' ha'
      exact congrArg Prod.snd (hgback i (t, a') ⟨ht, ha'⟩)
    have hd1 : deriv (fun a' => f (g i (t, a'))) a = 1 := hevent.deriv_eq.trans (deriv_id a)
    have hd0 := fderiv_comp_deriv a (hf.differentiableAt (by simp)) (hga.differentiableAt (by simp))
    exact one_ne_zero (by simpa only [hzero, map_zero] using hd1.symm.trans hd0)
  have hgzero (i : Fin 4) (a : ℝ) (ha : a ∈ J) : g i (0, a) = Bwall.chart ((1 + a) • port i) := by
    have haPos : 0 < 1 + a := by linarith [ha.1]
    rw [hg i (0, a) ⟨by dsimp [T]; constructor <;> linarith, ha⟩]
    apply congrArg P; apply N.injective
    change N (N (xi i (0, a))) = N (N (rho • J2 ((1 + a) • port i)))
    rw [(hN _).1, (hN _).1]
    have hh : Real.sqrt (rho ^ 2 * (1 + a) ^ 2 / 2) = rho * (1 + a) / Real.sqrt 2 := by
      apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
      symm
      rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      ring
    apply Prod.ext <;> simp [xi, port, map_smul, hh, smul_eq_mul] <;> ring
  have hgraph (s : ℝ × ℝ) (hs : s ∈ P.source) (t : ℝ) (ht : |t| < 8 * b) :
      L.symm (P s, c + t) ∈ S ↔ Q s = t := by
    have hw : (s, c + t) ∈ A.source := by
      rw [hAsource]; refine ⟨?_, ?_⟩
      · simpa only [hPsource, mem_ofPred_eq] using hs
      · change c - 8 * b < c + t ∧ c + t < c + 8 * b
        obtain ⟨hl, hu⟩ := abs_lt.mp ht; constructor <;> linarith
    obtain ⟨hAf, hh⟩ := hAform _ hw; rw [hAf] at hh
    change (L.symm (P s, c + t) ∈ S ↔
      c + t = c + D.morseSign1 * s.1 ^ 2 + D.morseSign2 * s.2 ^ 2) at hh
    constructor
    · intro hx; have := hh.mp hx; dsimp [Q]; linarith
    · intro hx; apply hh.mpr; dsimp [Q] at hx; linarith
  have hann (t : ℝ) (ht : t ∈ T) :
      {x : E2 | x ∈ Kann ∧ L.symm (x, c + t) ∈ S} = ⋃ i : Fin 4, (fun a => g i (t, a)) '' J := by
    ext x; constructor
    · rintro ⟨⟨v, hv, rfl⟩, hx⟩
      have hm := (hMann v).mp hv
      have hvsrc : v ∈ Bwall.chart.source := by
        rw [hBsource]
        exact mem_ball_zero_iff.mpr (by linarith [hv.2])
      have hq : Q (M v) = t := (hgraph _ hvsrc.2 t ((hTabs t ht).trans hdB)).mp hx
      obtain ⟨i, hi⟩ := hZcover (M v) hm.1 hm.2 (by rw [hq]; exact hTabs t ht)
      obtain ⟨hback, hright⟩ := hright i (M v) hi
      have hfirst : (back (M v)).1 = t := hq
      refine mem_iUnion.mpr ⟨i, (back (M v)).2, hback.2, ?_⟩
      have heq : (t, (back (M v)).2) = back (M v) := Prod.ext hfirst.symm rfl
      change g i (t, (back (M v)).2) = Bwall.chart v
      rw [heq, hg i _ hback, hright]; rfl
    · intro hx; obtain ⟨i, a, ha, rfl⟩ := mem_iUnion.mp hx
      have hp : (t, a) ∈ U := ⟨ht, ha⟩
      refine ⟨⟨M.symm (Y i (t, a)), ?_, ?_⟩, ?_⟩
      · apply (hMann _).mpr
        simpa only [M.apply_symm_apply] using ⟨(hYZ i _ hp).1, (hYZ i _ hp).2.1⟩
      · change P (M (M.symm (Y i (t, a)))) = g i (t, a)
        rw [M.apply_symm_apply, hg i _ hp]
      · change L.symm (g i (t, a), c + t) ∈ S
        rw [hg i _ hp]
        exact (hgraph _ (hYP i _ hp) t ((hTabs t ht).trans hdB)).mpr (hY i _ hp).2.1
  have hwall (t : ℝ) (ht : t ∈ T) :
      {x : E2 | x ∈ Bwall.boundary ∧ L.symm (x, c + t) ∈ S} =
        range (fun i : Fin 4 => g i (t, 0)) := by
    ext x; constructor
    · intro hx
      have hkan : x ∈ Kann := by
        rcases hx.1 with ⟨v, hv, rfl⟩
        exact ⟨v, by rw [mem_sphere_zero_iff_norm] at hv; constructor <;> linarith, rfl⟩
      have hh : x ∈ ⋃ i : Fin 4, (fun a => g i (t, a)) '' J := by
        rw [← hann t ht]
        exact ⟨hkan, hx.2⟩
      obtain ⟨i, a, ha, heq⟩ := mem_iUnion.mp hh
      change g i (t, a) = x at heq
      have ha0 : a = 0 := (hgtests i (t, a) ⟨ht, ha⟩).2.1.mp (by rw [heq]; exact hx.1)
      subst a; exact ⟨i, heq⟩
    · rintro ⟨i, rfl⟩
      have hp : (t, (0 : ℝ)) ∈ U := ⟨ht, by norm_num [J]⟩
      refine ⟨(hgtests i _ hp).2.1.mpr rfl, ?_⟩
      change L.symm (g i (t, 0), c + t) ∈ S
      rw [hg i _ hp]; exact (hgraph _ (hYP i _ hp) t ((hTabs t ht).trans hdB)).mpr (hY i _ hp).2.1
  have hwallI (t : ℝ) (ht : t ∈ T) : Injective (fun i : Fin 4 => g i (t, 0)) := by
    intro i k hik; by_contra hne
    have hp : (t, (0 : ℝ)) ∈ U := ⟨ht, by norm_num [J]⟩
    have heq : Y i (t, 0) = Y k (t, 0) := P.injOn (hYP i _ hp) (hYP k _ hp)
      (by rw [← hg i _ hp, ← hg k _ hp]; exact hik)
    exact disjoint_left.mp (hZd i k hne) (hYZ i _ hp) (heq.symm ▸ hYZ k _ hp)
  have hcentral : {x : E2 | x ∈ Bwall.closedRegion ∧ L.symm (x, c) ∈ S} =
      Bwall.chart '' {v : E2 | ‖v‖ ≤ 1 ∧ (J2 v).1 ^ 2 = (J2 v).2 ^ 2} := by
    ext x; constructor
    · rintro ⟨⟨v, hv, rfl⟩, hx⟩
      have hvsrc := Bwall.closedBall_subset_source hv
      change L.symm (P (M v), c) ∈ S at hx
      have hh := (hgraph (M v) hvsrc.2 0
        (by simpa using (mul_pos (by norm_num : (0 : ℝ) < 8) hb))).mp
        (by simpa only [add_zero] using hx)
      rw [hMQ] at hh
      exact ⟨v, ⟨mem_closedBall_zero_iff.mp hv,
        sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hrho2.ne')⟩, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      have hvsrc := Bwall.closedBall_subset_source (mem_closedBall_zero_iff.mpr hv.1)
      refine ⟨⟨v, mem_closedBall_zero_iff.mpr hv.1, rfl⟩, ?_⟩
      have hh := (hgraph (M v) hvsrc.2 0
        (by simpa using (mul_pos (by norm_num : (0 : ℝ) < 8) hb))).mpr
        (by rw [hMQ, hv.2, sub_self, mul_zero])
      change L.symm (P (M v), c) ∈ S
      simpa only [add_zero] using hh
  refine ⟨N, Bwall, E, hd, hdE, hdB, hdW, hdR, hmargin.1, hmargin.2,
    hN1, hNneg, hN, hBsource, hBtarget, fun _ => rfl, fun _ _ => rfl,
    hBbuffer, hBinside, hBclosed, hBboundary, hport, hportI,
    ?_, ?_, ?_, hann, hwall, hwallI, hcentral⟩
  · intro i
    refine ⟨hEs i, hEt i, hEm i, hEi i, hprotected i, ?_, ?_, hgs i, hradial i, hgzero i, hgtests i⟩
    · intro p hp
      exact ⟨rfl, hg i p hp, hgrec i p hp, (hroots p hp).1, (hroots p hp).2, hbuffer i p hp⟩
    · intro q hq; apply Prod.ext
      · change Q (D.morse q) = H (j q) - c
        have hh := D.morse_height q hq.1
        change H (j q) = c + D.morseSign1 * (D.morse q).1 ^ 2 +
          D.morseSign2 * (D.morse q).2 ^ 2 at hh
        dsimp [Q]; linarith
      · rfl
  · intro i k hik; apply disjoint_left.mpr; intro q hq hk
    exact disjoint_left.mp (hZd i k hik) hq.2 hk.2
  · ext q; constructor
    · intro hq; obtain ⟨i, hi⟩ := mem_iUnion.mp hq; exact ⟨hi.1, hi.2.1, hi.2.2.1, hi.2.2.2.1⟩
    · rintro ⟨hq, hl, hu, ht⟩; obtain ⟨i, hi⟩ := hZcover (D.morse q) hl hu ht
      exact mem_iUnion.mpr ⟨i, hq, hi⟩

end PoincareConjecture.M25.Topology3D
