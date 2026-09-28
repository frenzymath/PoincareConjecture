import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.SaddleEndpointOrientation
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.SaddlePortMatching
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.PieceData
import Mathlib.Analysis.Normed.Module.Connected










set_option autoImplicit false

open Set Filter Function
open scoped ContDiff Manifold InnerProductSpace Matrix Topology

namespace PoincareConjecture.M25.Topology3D

open SaddleOrientation

private theorem morse_radial_disc_isPreconnected (r : ℝ) (hr : 0 < r) :
    IsPreconnected {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 < r ^ 2} := by
  let e : E2 ≃L[ℝ] (ℝ × ℝ) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).trans
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)
  have he (x : E2) : ‖x‖ ^ 2 = (e x).1 ^ 2 + (e x).2 ^ 2 := by
    change ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2
    simpa only [Fin.sum_univ_two] using EuclideanSpace.real_norm_sq_eq x
  have hball : e '' Metric.ball (0 : E2) r =
      {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 < r ^ 2} := by
    ext s
    constructor
    · rintro ⟨x, hx, rfl⟩
      change (e x).1 ^ 2 + (e x).2 ^ 2 < r ^ 2
      rw [← he]
      exact (sq_lt_sq₀ (norm_nonneg x) hr.le).mpr (mem_ball_zero_iff.mp hx)
    · intro hs
      change s.1 ^ 2 + s.2 ^ 2 < r ^ 2 at hs
      refine ⟨e.symm s, mem_ball_zero_iff.mpr ?_, e.apply_symm_apply s⟩
      apply (sq_lt_sq₀ (norm_nonneg _) hr.le).mp
      simpa only [he, e.apply_symm_apply] using hs
  rw [← hball]
  exact Metric.isPreconnected_ball.image e e.continuous.continuousOn



theorem exists_saddle_exterior_upper_matching
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
        s.1 ^ 2 - s.2 ^ 2)
    (alpha : Fin 2 → ℝ → UnitTwoSphere)
    (ha : ∀ k, ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ∞ (alpha k) ∧
      ∀ t, Injective (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (alpha k) t))
    (hlevel : ∀ k t, ⟪(u : E3), psi (alpha k t, 0)⟫_ℝ =
      ⟪(u : E3), psi (D.point, 0)⟫_ℝ - delta)
    (ends : Fin 2 × Fin 2 ≃ Fin 4) (eta : ℝ) (heta : 0 < eta) :
    let r : ℝ := 5 * R / 8
    let aa := Real.sqrt ((r ^ 2 - delta) / 2)
    let bb := Real.sqrt ((r ^ 2 + delta) / 2)
    let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
    let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
    let p : Fin 4 → UnitTwoSphere := fun i =>
      D.morse.symm (N (sx i * aa, sy i * bb))
    let ep : Fin 2 × Fin 2 ≃ Fin 4 := finProdFinEquiv
    let other : Fin 2 → Fin 2 := ![1, 0]
    (∀ k, alpha k 0 = p (ends (k, 0)) ∧ alpha k 1 = p (ends (k, 1))) →
    (∀ k, Disjoint (alpha k '' Ioo (0 : ℝ) 1)
      (D.morse.symm '' {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 ≤ r ^ 2})) →
    (∀ k, ∀ t ∈ Ioo (1 : ℝ) (1 + eta),
      alpha k t ∈ D.morse.symm '' {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 < r ^ 2}) →
    (∀ k, (ep.symm (ends (k, 0))).1 ≠ (ep.symm (ends (k, 1))).1) →
    ∃ label : Fin 2 ≃ Fin 2, ∀ k,
      ({ends (k, 0), ends (k, 1)} : Set (Fin 4)) =
        {ep (label k, 0), ep (other (label k), 1)} := by
  classical
  dsimp only
  let r : ℝ := 5 * R / 8
  let aa := Real.sqrt ((r ^ 2 - delta) / 2)
  let bb := Real.sqrt ((r ^ 2 + delta) / 2)
  let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
  let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
  let pm : Fin 4 → ℝ × ℝ := fun i => (sx i * aa, sy i * bb)
  let p : Fin 4 → UnitTwoSphere := fun i => D.morse.symm (N (pm i))
  intro hend houtside hafter hparent
  have hr : 0 < r := by dsimp [r]; positivity
  have hdsmall : delta < r ^ 2 := by
    change delta ≤ r ^ 2 / 128 at hdR
    nlinarith [sq_pos_of_pos hr]
  have hrbig : r ^ 2 < (2 * R) ^ 2 := by dsimp [r]; nlinarith [sq_pos_of_pos hR]
  have haa : aa ^ 2 = (r ^ 2 - delta) / 2 :=
    Real.sq_sqrt (by linarith)
  have hbb : bb ^ 2 = (r ^ 2 + delta) / 2 :=
    Real.sq_sqrt (by positivity)
  have haapos : 0 < aa := Real.sqrt_pos.mpr (by linarith)
  have hbbpos : 0 < bb := Real.sqrt_pos.mpr (by positivity)
  have hpm (i : Fin 4) :
      (pm i).1 ^ 2 + (pm i).2 ^ 2 = r ^ 2 ∧
      (pm i).1 ≠ 0 ∧ (pm i).2 ≠ 0 := by
    fin_cases i <;> simp [pm, sx, sy, ne_of_gt haapos, ne_of_gt hbbpos] <;>
      nlinarith [haa, hbb]
  let M := N.toHomeomorph.toOpenPartialHomeomorph.trans D.morse.symm
  have hMs : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ M M.source :=
    D.morse_inverse.comp N.contDiff.contMDiff.contMDiffOn (fun _ hs => hs.2)
  have hMi : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ M.symm M.target :=
    N.symm.contDiff.contMDiff.comp_contMDiffOn
      (D.morse_smooth.mono inter_subset_left)
  let c := ⟪(u : E3), psi (D.point, 0)⟫_ℝ
  have hheight (s : ℝ × ℝ) (hs : s ∈ M.source) :
      ⟪(u : E3), psi (M s, 0)⟫_ℝ = c + s.1 ^ 2 - s.2 ^ 2 := by
    have hsN : N s ∈ D.morse.target := hs.2
    have hm := D.morse_height (D.morse.symm (N s)) (D.morse.map_target hsN)
    rw [D.morse.right_inv hsN] at hm
    change ⟪(u : E3), psi (M s, 0)⟫_ℝ = c +
      D.morseSign1 * (N s).1 ^ 2 + D.morseSign2 * (N s).2 ^ 2 at hm
    linarith only [hm, (hN s).2.2]
  let W : Set (ℝ × ℝ) := {s | s.1 ^ 2 + s.2 ^ 2 < (2 * R) ^ 2}
  have hWsource : W ⊆ M.source := by
    intro s hs
    refine ⟨mem_univ _, hmorse ?_⟩
    change (N s).1 ^ 2 + (N s).2 ^ 2 < (2 * R) ^ 2
    rw [(hN s).2.1]
    exact hs
  have hW : IsPreconnected W :=
    morse_radial_disc_isPreconnected (2 * R) (by positivity)
  have hpmW (i : Fin 4) : pm i ∈ W := by
    change (pm i).1 ^ 2 + (pm i).2 ^ 2 < (2 * R) ^ 2
    rw [(hpm i).1]
    exact hrbig
  have hpTarget (i : Fin 4) : p i ∈ M.target := M.map_source (hWsource (hpmW i))
  have hpCoord (i : Fin 4) : M.symm (p i) = pm i := M.left_inv (hWsource (hpmW i))
  have hdisc : {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 ≤ r ^ 2} ⊆ M.source := by
    intro s hs
    exact hWsource ((show s.1 ^ 2 + s.2 ^ 2 ≤ r ^ 2 from hs).trans_lt hrbig)
  have hnormalize (Z : Set (ℝ × ℝ)) (hZ : ∀ s, s ∈ Z ↔ N s ∈ Z) :
      D.morse.symm '' Z = M '' Z := by
    ext q
    constructor
    · rintro ⟨s, hs, rfl⟩
      refine ⟨N s, (hZ s).mp hs, ?_⟩
      change D.morse.symm (N (N s)) = D.morse.symm s
      rw [(hN s).1]
    · rintro ⟨s, hs, rfl⟩
      exact ⟨N s, (hZ s).mp hs, rfl⟩
  have hclosed := hnormalize {s | s.1 ^ 2 + s.2 ^ 2 ≤ r ^ 2} (fun s => by
    change s.1 ^ 2 + s.2 ^ 2 ≤ r ^ 2 ↔ (N s).1 ^ 2 + (N s).2 ^ 2 ≤ r ^ 2
    rw [(hN s).2.1])
  have hopen := hnormalize {s | s.1 ^ 2 + s.2 ^ 2 < r ^ 2} (fun s => by
    change s.1 ^ 2 + s.2 ^ 2 < r ^ 2 ↔ (N s).1 ^ 2 + (N s).2 ^ 2 < r ^ 2
    rw [(hN s).2.1])
  have hends (k : Fin 2) (t : ℝ) (ht : t ∈ ({0, 1} : Set ℝ)) :
      ∃ i : Fin 4, alpha k t = p i := by
    simp only [mem_insert_iff, mem_singleton_iff] at ht
    rcases ht with rfl | rfl
    · exact ⟨ends (k, 0), (hend k).1⟩
    · exact ⟨ends (k, 1), (hend k).2⟩
  have hreg (k : Fin 2) (t : ℝ) :
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
        (fun q : UnitTwoSphere => ⟪(u : E3), psi (q, 0)⟫_ℝ) (alpha k t) ≠ 0 := by
    have hc : alpha k t ∈ D.sourceCore := hcore _ (by
      rw [hlevel]
      change |c - delta - c| ≤ 3 * delta
      rw [sub_sub_cancel_left, abs_neg, abs_of_pos hd]
      linarith)
    intro hz
    have heq := (D.unique_critical _ hc).mp hz
    have hh := hlevel k t
    rw [heq] at hh
    linarith
  obtain ⟨defining, hdefining, hdefiningPsi, hdefiningNz⟩ :=
    exists_sphere_collar_defining_function psi hpsi
  have hproducts (k : Fin 2) :
      ((pm (ends (k, 0))).1 * (pm (ends (k, 0))).2) *
        ((pm (ends (k, 1))).1 * (pm (ends (k, 1))).2) < 0 := by
    have hh := saddle_arc_opposite_port_products psi hpsi
      defining hdefining hdefiningPsi hdefiningNz (u : E3) c (c - delta)
      M hMs hMi hheight W hW hWsource (alpha k) (ha k).1 (ha k).2
      (hlevel k) (hreg k) r eta heta hdisc
      (fun t ht => by
        obtain ⟨i, hi⟩ := hends k t ht
        rw [hi]
        exact hpTarget i)
      (fun t ht => by
        obtain ⟨i, hi⟩ := hends k t ht
        rw [hi, hpCoord]
        exact hpmW i)
      (fun t ht => by
        obtain ⟨i, hi⟩ := hends k t ht
        rw [hi, hpCoord]
        exact (hpm i).1)
      (fun t ht => by
        obtain ⟨i, hi⟩ := hends k t ht
        rw [hi, hpCoord]
        exact (hpm i).2)
      (by rw [← hclosed]; exact houtside k)
      (fun t ht => by rw [← hopen]; exact hafter k t ht)
    rw [(hend k).1, (hend k).2, hpCoord, hpCoord] at hh
    exact hh
  exact exists_upper_arc_matching ends hparent (fun k =>
    port_sign_product_neg_of_scaled aa bb
      (sx (ends (k, 0))) (sy (ends (k, 0)))
      (sx (ends (k, 1))) (sy (ends (k, 1))) (hproducts k))

end PoincareConjecture.M25.Topology3D
