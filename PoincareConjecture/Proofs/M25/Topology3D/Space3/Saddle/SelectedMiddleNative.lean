import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.SelectedSourceGeometry
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.SelectedSourceChart
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.SelectedWallTransport










set_option autoImplicit false

open Set Metric Function Filter
open scoped ContDiff Manifold InnerProductSpace Topology Matrix NNReal

namespace PoincareConjecture.M25.Topology3D




theorem saddle_selected_middle_native
    (psi : UnitTwoSphere × ℝ → E3) (u : UnitTwoSphere)
    (D : SaddlePieceData psi u)
    (R b delta : ℝ) (hR : 0 < R) (hdelta : 0 < delta)
    (hwindow : 2 * delta < 8 * b)
    (hsmall : delta ≤ (5 * R / 8) ^ 2 / 128)
    (P : OpenPartialHomeomorph (ℝ × ℝ) E2)
    (A : OpenPartialHomeomorph ((ℝ × ℝ) × ℝ) E3)
    (hAsource : A.source =
      {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 < (2 * R) ^ 2} ×ˢ
        Ioo (⟪(u : E3), psi (D.point, 0)⟫_ℝ - 8 * b)
          (⟪(u : E3), psi (D.point, 0)⟫_ℝ + 8 * b))
    (hAgraph : ∀ w ∈ A.source,
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
    (hkp : ∀ x : E2, kp x = P (N ((5 * R / 8) • J2 x)))
    (gRef : Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
    (hgRef : EqOn gRef kp (closedBall (0 : E2) 2))
    (ks : OpenPartialHomeomorph E2 UnitTwoSphere)
    (hksForm : ∀ x : E2,
      ks x = D.morse.symm (N ((5 * R / 8) • J2 x)))
    (X : E3 → E3) (K B : ℝ≥0)
    (hK : LipschitzWith K X) (hB : ∀ y, ‖X y‖ ≤ B)
    (hX : ContDiff ℝ ∞ X) (hcX : HasCompactSupport X) :
    let j : UnitTwoSphere → E3 := fun p => psi (p, 0)
    let pi := horizontalBandProjection u
    let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
    let c := H (j D.point)
    let rho := 5 * R / 8
    let L := heightPlaneCoordinates u
    let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
    let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
    let xi : Fin 4 → ℝ → ℝ → E2 := fun k t r => J2.symm
      (sx k * Real.sqrt ((r ^ 2 + t / rho ^ 2) / 2),
        sy k * Real.sqrt ((r ^ 2 - t / rho ^ 2) / 2))
    let Xi : Fin 4 → ℝ → ℝ → E3 := fun k t r =>
      L.symm (gRef (xi k t r), c + t)
    let q : Fin 4 → (ℝ × ℝ) → UnitTwoSphere := fun k p =>
      D.morse.symm (N
        (sx k * Real.sqrt ((rho ^ 2 * (1 + p.2) ^ 2 + p.1) / 2),
          sy k * Real.sqrt ((rho ^ 2 * (1 + p.2) ^ 2 - p.1) / 2)))
    let Phi : ℝ → Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞ :=
      fun t => boundedFlowDiffeomorph X hK hB hX hcX t
    ∀ (_hCoordinates : ∀ x ∈ closedBall (0 : E2) 2,
        pi (j (ks x)) = kp x ∧
        H (j (ks x)) = c + rho ^ 2 * ((J2 x).1 ^ 2 - (J2 x).2 ^ 2))
      (_hNative : ∀ k : Fin 4, ∀ a : ℝ, |a| < 1 / 8 →
        ∀ s t : ℝ, |s| ≤ 2 * delta → |t| ≤ 2 * delta →
          Phi (t - s) (j (q k (s, a))) = j (q k (t, a))),
      (∀ t : ℝ, |t| < 2 * delta → ∀ x : E2, ‖x‖ < 2 →
        (L.symm (gRef x, c + t) ∈ range j ↔
          t = rho ^ 2 * ((J2 x).1 ^ 2 - (J2 x).2 ^ 2))) ∧
      (∀ (k : Fin 4) (r : ℝ), r ∈ Ioo (15 / 16 : ℝ) (17 / 16) →
        ∀ t : ℝ, |t| < 2 * delta →
          HasDerivAt (fun s : ℝ => Xi k s r) (X (Xi k t r)) t) := by
  dsimp only
  intro hCoordinates hNative
  let j : UnitTwoSphere → E3 := fun p => psi (p, 0)
  let pi := horizontalBandProjection u
  let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
  let c := H (j D.point)
  let rho := 5 * R / 8
  let L := heightPlaneCoordinates u
  let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
  let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
  let xi : Fin 4 → ℝ → ℝ → E2 := fun k t r => J2.symm
    (sx k * Real.sqrt ((r ^ 2 + t / rho ^ 2) / 2),
      sy k * Real.sqrt ((r ^ 2 - t / rho ^ 2) / 2))
  let Xi : Fin 4 → ℝ → ℝ → E3 := fun k t r =>
    L.symm (gRef (xi k t r), c + t)
  let q : Fin 4 → (ℝ × ℝ) → UnitTwoSphere := fun k p =>
    D.morse.symm (N
      (sx k * Real.sqrt ((rho ^ 2 * (1 + p.2) ^ 2 + p.1) / 2),
        sy k * Real.sqrt ((rho ^ 2 * (1 + p.2) ^ 2 - p.1) / 2)))
  let Phi : ℝ → Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞ :=
    fun t => boundedFlowDiffeomorph X hK hB hX hcX t
  change ∀ x ∈ closedBall (0 : E2) 2,
    pi (j (ks x)) = kp x ∧
    H (j (ks x)) = c + rho ^ 2 * ((J2 x).1 ^ 2 - (J2 x).2 ^ 2) at hCoordinates
  change ∀ k : Fin 4, ∀ a : ℝ, |a| < 1 / 8 →
    ∀ s t : ℝ, |s| ≤ 2 * delta → |t| ≤ 2 * delta →
      Phi (t - s) (j (q k (s, a))) = j (q k (t, a)) at hNative
  have hrho : 0 < rho := by dsimp only [rho]; positivity
  have hrho2 : 0 < rho ^ 2 := sq_pos_of_pos hrho
  let M : E2 → ℝ × ℝ := fun x => N (rho • J2 x)
  have hMr (x : E2) :
      (M x).1 ^ 2 + (M x).2 ^ 2 = rho ^ 2 * ‖x‖ ^ 2 := by
    change (N (rho • J2 x)).1 ^ 2 + (N (rho • J2 x)).2 ^ 2 = _
    rw [(hN _).1]
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    rw [← hJ2]
    ring
  have hMQ (x : E2) :
      D.morseSign1 * (M x).1 ^ 2 + D.morseSign2 * (M x).2 ^ 2 =
        rho ^ 2 * ((J2 x).1 ^ 2 - (J2 x).2 ^ 2) := by
    change D.morseSign1 * (N (rho • J2 x)).1 ^ 2 +
      D.morseSign2 * (N (rho • J2 x)).2 ^ 2 = _
    rw [(hN _).2]
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  have hGraph (t : ℝ) (ht : |t| < 2 * delta) (x : E2) (hx : ‖x‖ < 2) :
      L.symm (gRef x, c + t) ∈ range j ↔
        t = rho ^ 2 * ((J2 x).1 ^ 2 - (J2 x).2 ^ 2) := by
    have hx2 : x ∈ closedBall (0 : E2) 2 := mem_closedBall_zero_iff.mpr hx.le
    have hrad : (M x).1 ^ 2 + (M x).2 ^ 2 < (2 * R) ^ 2 := by
      rw [hMr]
      have hsq : ‖x‖ ^ 2 ≤ 4 := by nlinarith only [hx, norm_nonneg x]
      have hmul := mul_le_mul_of_nonneg_left hsq hrho2.le
      have hmargin : rho ^ 2 * 4 < (2 * R) ^ 2 := by
        dsimp only [rho]
        nlinarith only [sq_pos_of_pos hR]
      exact hmul.trans_lt hmargin
    have hw : (M x, c + t) ∈ A.source := by
      rw [hAsource]
      refine ⟨hrad, ?_⟩
      change c - 8 * b < c + t ∧ c + t < c + 8 * b
      exact ⟨by linarith only [(abs_lt.mp ht).1, hwindow],
        by linarith only [(abs_lt.mp ht).2, hwindow]⟩
    have hform : A (M x, c + t) = L.symm (gRef x, c + t) := by
      rw [(hAgraph _ hw).1, hgRef hx2, hkp]
    have hiff := (hAgraph _ hw).2
    rw [hform] at hiff
    change (L.symm (gRef x, c + t) ∈ range j ↔
      c + t = c + D.morseSign1 * (M x).1 ^ 2 +
        D.morseSign2 * (M x).2 ^ 2) at hiff
    refine hiff.trans ?_
    constructor <;> intro hh <;> linarith only [hh, hMQ x]
  obtain ⟨-, -, hBranch⟩ := saddle_selected_source_geometry
    psi u D rho hrho J2 hJ2 N (fun s => (hN s).1) ks hksForm
  have hsign (k : Fin 4) : (sx k) ^ 2 = 1 ∧ (sy k) ^ 2 = 1 := by
    fin_cases k <;> norm_num [sx, sy]
  have hxi (k : Fin 4) (r : ℝ) (hr : r ∈ Ioo (15 / 16 : ℝ) (17 / 16))
      (t : ℝ) (ht : |t| < 2 * delta) :
      ‖xi k t r‖ = r ∧
        rho ^ 2 * ((J2 (xi k t r)).1 ^ 2 - (J2 (xi k t r)).2 ^ 2) = t := by
    have hsmall' : delta ≤ rho ^ 2 / 128 := hsmall
    have hquot : |t / rho ^ 2| < 1 / 64 := by
      rw [abs_div, abs_of_pos hrho2]
      apply (div_lt_iff₀ hrho2).mpr
      linarith only [ht, hsmall']
    have hp : 0 ≤ (r ^ 2 + t / rho ^ 2) / 2 := by
      nlinarith only [hr.1, (abs_lt.mp hquot).1, sq_nonneg (r - 15 / 16)]
    have hm : 0 ≤ (r ^ 2 - t / rho ^ 2) / 2 := by
      nlinarith only [hr.1, (abs_lt.mp hquot).2, sq_nonneg (r - 15 / 16)]
    have hx0 : (J2 (xi k t r)).1 ^ 2 = (r ^ 2 + t / rho ^ 2) / 2 := by
      simp only [xi, ContinuousLinearEquiv.apply_symm_apply, mul_pow,
        (hsign k).1, one_mul, Real.sq_sqrt hp]
    have hx1 : (J2 (xi k t r)).2 ^ 2 = (r ^ 2 - t / rho ^ 2) / 2 := by
      simp only [xi, ContinuousLinearEquiv.apply_symm_apply, mul_pow,
        (hsign k).2, one_mul, Real.sq_sqrt hm]
    have hnorm : ‖xi k t r‖ ^ 2 = r ^ 2 := by rw [← hJ2, hx0, hx1]; ring
    refine ⟨by nlinarith only [hnorm, norm_nonneg (xi k t r), hr.1], ?_⟩
    rw [hx0, hx1]
    field_simp
    ring
  have hPoint (k : Fin 4) (r : ℝ) (hr : r ∈ Ioo (15 / 16 : ℝ) (17 / 16))
      (t : ℝ) (ht : |t| < 2 * delta) : j (q k (t, r - 1)) = Xi k t r := by
    have hrad := hxi k r hr t ht
    have hx2 : xi k t r ∈ closedBall (0 : E2) 2 :=
      mem_closedBall_zero_iff.mpr (by rw [hrad.1]; linarith only [hr.2])
    have hnative : ks (xi k t r) = q k (t, r - 1) := by
      have he := hBranch t r k
      have hr1 : 1 + (r - 1) = r := by ring
      simpa only [xi, q, sx, sy, hr1] using he
    have hcoord := hCoordinates (xi k t r) hx2
    rw [hnative] at hcoord
    apply L.injective
    change L (j (q k (t, r - 1))) = L (L.symm (gRef (xi k t r), c + t))
    rw [L.apply_symm_apply]
    apply Prod.ext
    · exact hcoord.1.trans (hgRef hx2).symm
    · have hh := hcoord.2
      rw [hrad.2] at hh
      simpa only [H, L, InnerProductSpace.toDual_apply_apply,
        heightPlaneCoordinates_snd] using hh
  have hzero : |(0 : ℝ)| ≤ 2 * delta := by rw [abs_zero]; positivity
  have hFlow (k : Fin 4) (r : ℝ) (hr : r ∈ Ioo (15 / 16 : ℝ) (17 / 16))
      (t : ℝ) (ht : |t| < 2 * delta) :
      boundedFlow X hK hB (j (q k (0, r - 1))) t = Xi k t r := by
    have ha : |r - 1| < 1 / 8 := abs_lt.mpr
      ⟨by linarith only [hr.1], by linarith only [hr.2]⟩
    have he := hNative k (r - 1) ha 0 t hzero ht.le
    change boundedFlow X hK hB (j (q k (0, r - 1))) (t - 0) =
      j (q k (t, r - 1)) at he
    have he' : boundedFlow X hK hB (j (q k (0, r - 1))) t =
        j (q k (t, r - 1)) := by simpa only [sub_zero] using he
    exact he'.trans (hPoint k r hr t ht)
  refine ⟨hGraph, ?_⟩
  intro k r hr t ht
  change HasDerivAt (fun s : ℝ => Xi k s r) (X (Xi k t r)) t
  have heq : (fun s : ℝ => Xi k s r) =ᶠ[𝓝 t]
      boundedFlow X hK hB (j (q k (0, r - 1))) := by
    filter_upwards [Ioo_mem_nhds (abs_lt.mp ht).1 (abs_lt.mp ht).2] with s hs
    exact (hFlow k r hr s (abs_lt.mpr hs)).symm
  have hder := boundedFlow_hasDerivAt X hK hB (j (q k (0, r - 1))) t
  rw [hFlow k r hr t ht] at hder
  exact hder.congr_of_eventuallyEq heq

end PoincareConjecture.M25.Topology3D
