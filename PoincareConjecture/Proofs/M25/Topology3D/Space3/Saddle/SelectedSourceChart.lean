import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.PieceData
import PoincareConjecture.Proofs.M25.Topology3D.Space3.HorizontalBandField
import Mathlib.Tactic

set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

theorem exists_saddle_selected_source_chart
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (u : UnitTwoSphere) (D : SaddlePieceData psi u)
    (R b delta : ℝ) (hR : 0 < R) (hwindow : 2 * delta < 8 * b)
    (P : OpenPartialHomeomorph (ℝ × ℝ) E2)
    (A : OpenPartialHomeomorph ((ℝ × ℝ) × ℝ) E3)
    (hPsource : P.source =
      {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 < (2 * R) ^ 2})
    (hPmorse : P.source ⊆ D.morse.target)
    (hPform : ∀ s ∈ P.source,
      P s = horizontalBandProjection u (psi (D.morse.symm s, 0)))
    (hAsource : A.source =
      {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 < (2 * R) ^ 2} ×ˢ
        Ioo (⟪(u : E3), psi (D.point, 0)⟫_ℝ - 8 * b)
          (⟪(u : E3), psi (D.point, 0)⟫_ℝ + 8 * b))
    (hAform : ∀ w ∈ A.source,
      A w = (heightPlaneCoordinates u).symm (P w.1, w.2) ∧
      (A w ∈ range (fun q : UnitTwoSphere => psi (q, 0)) ↔
        w.2 = ⟪(u : E3), psi (D.point, 0)⟫_ℝ +
          D.morseSign1 * w.1.1 ^ 2 + D.morseSign2 * w.1.2 ^ 2))
    (J2 : E2 ≃L[ℝ] (ℝ × ℝ))
    (hJ2 : ∀ x : E2, (J2 x).1 ^ 2 + (J2 x).2 ^ 2 = ‖x‖ ^ 2)
    (N : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ))
    (hN : ∀ s : ℝ × ℝ,
      (N s).1 ^ 2 + (N s).2 ^ 2 = s.1 ^ 2 + s.2 ^ 2 ∧
      D.morseSign1 * (N s).1 ^ 2 + D.morseSign2 * (N s).2 ^ 2 =
        s.1 ^ 2 - s.2 ^ 2)
    (kp : OpenPartialHomeomorph E2 E2)
    (hkp : ∀ x : E2, kp x = P (N ((5 * R / 8) • J2 x))) :
    let j : UnitTwoSphere → E3 := fun p => psi (p, 0)
    let pi := horizontalBandProjection u
    let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
    let c := H (j D.point)
    let rho := 5 * R / 8
    ∃ ks : OpenPartialHomeomorph E2 UnitTwoSphere,
      ks.source = {x : E2 | N (rho • J2 x) ∈ D.morse.target} ∧
      ks.target = D.morse.source ∧
      (∀ x : E2, ks x = D.morse.symm (N (rho • J2 x))) ∧
      (∀ p : UnitTwoSphere,
        ks.symm p = J2.symm (rho⁻¹ • N.symm (D.morse p))) ∧
      closedBall (0 : E2) 2 ⊆ ks.source ∧
      ContMDiffOn 𝓘(ℝ, E2) (𝓡 2) ∞ ks ks.source ∧
      ContMDiffOn (𝓡 2) 𝓘(ℝ, E2) ∞ ks.symm ks.target ∧
      (∀ x ∈ closedBall (0 : E2) 2,
        pi (j (ks x)) = kp x ∧
        H (j (ks x)) = c + rho ^ 2 * ((J2 x).1 ^ 2 - (J2 x).2 ^ 2)) ∧
      (∀ z : ℝ, |z| ≤ 2 * delta → ∀ p : UnitTwoSphere,
        H (j p) = c + z →
        (pi (j p) ∈ kp '' ball (0 : E2) 1 ↔
          p ∈ ks '' ball (0 : E2) 1) ∧
        (pi (j p) ∈ kp '' closedBall (0 : E2) 1 ↔
          p ∈ ks '' closedBall (0 : E2) 1)) := by
  let j : UnitTwoSphere → E3 := fun p => psi (p, 0)
  let pi := horizontalBandProjection u
  let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
  let c := H (j D.point)
  let rho := 5 * R / 8
  let L := heightPlaneCoordinates u
  let r2 : ℝ × ℝ → ℝ := fun s => s.1 ^ 2 + s.2 ^ 2
  let Q : ℝ × ℝ → ℝ := fun s =>
    D.morseSign1 * s.1 ^ 2 + D.morseSign2 * s.2 ^ 2
  have hrho : 0 < rho := by dsimp [rho]; positivity
  let M : E2 ≃L[ℝ] (ℝ × ℝ) := {
    toFun := fun x => N (rho • J2 x)
    invFun := fun s => J2.symm (rho⁻¹ • N.symm s)
    map_add' := by intros; simp [map_add, smul_add]
    map_smul' := by intros; simp [map_smul, smul_smul, mul_comm]
    left_inv := by
      intro x
      change J2.symm (rho⁻¹ • N.symm (N (rho • J2 x))) = x
      rw [N.symm_apply_apply, inv_smul_smul₀ hrho.ne', J2.symm_apply_apply]
    right_inv := by
      intro s
      change N (rho • J2 (J2.symm (rho⁻¹ • N.symm s))) = s
      rw [J2.apply_symm_apply, smul_inv_smul₀ hrho.ne', N.apply_symm_apply]
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  let ks := M.toHomeomorph.toOpenPartialHomeomorph.trans D.morse.symm
  have hsource : ks.source = {x : E2 | N (rho • J2 x) ∈ D.morse.target} := by
    ext x
    change (x ∈ univ ∧ N (rho • J2 x) ∈ D.morse.target) ↔ _
    simp only [mem_univ, true_and, mem_ofPred_eq]
  have htarget : ks.target = D.morse.source := by
    ext p
    change (p ∈ D.morse.source ∧ D.morse p ∈ univ) ↔ _
    simp only [mem_univ, and_true]
  have hks : ContMDiffOn 𝓘(ℝ, E2) (𝓡 2) ∞ ks ks.source :=
    D.morse_inverse.comp M.contDiff.contMDiff.contMDiffOn (fun _ hx => hx.2)
  have hksInv : ContMDiffOn (𝓡 2) 𝓘(ℝ, E2) ∞ ks.symm ks.target :=
    M.symm.contDiff.contMDiff.comp_contMDiffOn
      (D.morse_smooth.mono inter_subset_left)
  have hMr (x : E2) : r2 (M x) = rho ^ 2 * ‖x‖ ^ 2 := by
    calc
      r2 (M x) = rho ^ 2 * ((J2 x).1 ^ 2 + (J2 x).2 ^ 2) := by
        change (N (rho • J2 x)).1 ^ 2 + (N (rho • J2 x)).2 ^ 2 = _
        rw [(hN _).1]
        simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        ring
      _ = rho ^ 2 * ‖x‖ ^ 2 := by rw [hJ2]
  have hMQ (x : E2) : Q (M x) =
      rho ^ 2 * ((J2 x).1 ^ 2 - (J2 x).2 ^ 2) := by
    change D.morseSign1 * (N (rho • J2 x)).1 ^ 2 +
      D.morseSign2 * (N (rho • J2 x)).2 ^ 2 = _
    rw [(hN _).2]
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  have hMP (x : E2) (hx : x ∈ closedBall (0 : E2) 2) : M x ∈ P.source := by
    rw [hPsource]
    change r2 (M x) < (2 * R) ^ 2
    rw [hMr]
    have hn : ‖x‖ ≤ 2 := mem_closedBall_zero_iff.mp hx
    have hsq : ‖x‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg x]
    have hmul := mul_le_mul_of_nonneg_left hsq (sq_nonneg rho)
    have hmargin : rho ^ 2 * 4 < (2 * R) ^ 2 := by
      dsimp [rho]
      nlinarith [sq_pos_of_pos hR]
    exact hmul.trans_lt hmargin
  have hbuffer : closedBall (0 : E2) 2 ⊆ ks.source := by
    intro x hx
    exact ⟨mem_univ _, hPmorse (hMP x hx)⟩
  have hcoordinates (x : E2) (hx : x ∈ closedBall (0 : E2) 2) :
      pi (j (ks x)) = kp x ∧
      H (j (ks x)) = c + rho ^ 2 * ((J2 x).1 ^ 2 - (J2 x).2 ^ 2) := by
    have hPx := hMP x hx
    have hMx := hPmorse hPx
    constructor
    · exact (hPform (M x) hPx).symm.trans (hkp x).symm
    · have hh := D.morse_height (D.morse.symm (M x)) (D.morse.map_target hMx)
      rw [D.morse.right_inv hMx] at hh
      change H (j (ks x)) = c + D.morseSign1 * (M x).1 ^ 2 +
        D.morseSign2 * (M x).2 ^ 2 at hh
      have hq := hMQ x
      dsimp only [Q] at hq
      linarith
  have hji : Injective j := by
    intro p q hpq
    exact congrArg Prod.fst (hpsi.2.1 (x₁ := (p, 0)) (x₂ := (q, 0))
      ⟨mem_univ _, by norm_num⟩ ⟨mem_univ _, by norm_num⟩ hpq)
  have h12 : closedBall (0 : E2) 1 ⊆ closedBall (0 : E2) 2 :=
    closedBall_subset_closedBall (by norm_num)
  have hidentify (z : ℝ) (hz : |z| ≤ 2 * delta) (p : UnitTwoSphere)
      (hp : H (j p) = c + z) (x : E2) (hx : x ∈ closedBall (0 : E2) 1)
      (hpx : pi (j p) = kp x) : p = ks x := by
    have hx2 := h12 hx
    have hPx := hMP x hx2
    have hw : (M x, c + z) ∈ A.source := by
      rw [hAsource]
      refine ⟨?_, ?_⟩
      · simpa only [hPsource] using hPx
      · change c - 8 * b < c + z ∧ c + z < c + 8 * b
        have hzz := abs_le.mp hz
        constructor <;> linarith
    have hAp : A (M x, c + z) = j p := by
      rw [(hAform (M x, c + z) hw).1]
      change L.symm (P (M x), c + z) = j p
      have hPk : kp x = P (M x) := hkp x
      rw [← hPk, ← hpx]
      exact heightPlaneCoordinates_reconstruct u (j p) (c + z) hp
    have hgraph := (hAform (M x, c + z) hw).2.mp (by
      rw [hAp]
      exact mem_range_self p)
    change c + z = c + D.morseSign1 * (M x).1 ^ 2 +
      D.morseSign2 * (M x).2 ^ 2 at hgraph
    have hq := hMQ x
    dsimp only [Q] at hq
    have hheight : H (j p) = H (j (ks x)) := by
      rw [hp, (hcoordinates x hx2).2]
      linarith
    apply hji
    apply L.injective
    apply Prod.ext
    · exact hpx.trans (hcoordinates x hx2).1.symm
    · simpa only [L, H, InnerProductSpace.toDual_apply_apply,
        heightPlaneCoordinates_snd] using hheight
  refine ⟨ks, hsource, htarget, (fun _ => rfl), (fun _ => rfl),
    hbuffer, hks, hksInv, hcoordinates, ?_⟩
  intro z hz p hp
  constructor
  · constructor
    · rintro ⟨x, hx, hpx⟩
      exact ⟨x, hx, (hidentify z hz p hp x (ball_subset_closedBall hx) hpx.symm).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, (hcoordinates x (h12 (ball_subset_closedBall hx))).1.symm⟩
  · constructor
    · rintro ⟨x, hx, hpx⟩
      exact ⟨x, hx, (hidentify z hz p hp x hx hpx.symm).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, (hcoordinates x (h12 hx)).1.symm⟩

end PoincareConjecture.M25.Topology3D
