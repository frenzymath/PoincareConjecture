import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NestedReferenceBufferedChart
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.PlanarBallChartExtension
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.BallTransport
import PoincareConjecture.Proofs.M25.Topology3D.Space3.HeightPlaneProjection
import Mathlib.Tactic










set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D.NestedReferenceLower




theorem exists_reference_placement
    (w : ℝ) (hw_lower : 1 / 2 < w) (hw_upper : w < 3 / 4)
    (m : OpenPartialHomeomorph E2 (ℝ × ℝ))
    (hm_point : (!₂[-Real.sqrt (1 - w ^ 2), 0] : E2) ∈ m.source)
    (hm_source : m.source ⊆ Metric.ball (0 : E2) 1)
    (hm_zero : m (!₂[-Real.sqrt (1 - w ^ 2), 0] : E2) = 0)
    (hm : ContDiffOn ℝ ∞ m m.source)
    (hmi : ContDiffOn ℝ ∞ m.symm m.target)
    (hm_height : ∀ v ∈ m.source,
      ‖v‖ ^ 2 + Real.sqrt (1 - ‖v‖ ^ 2) + v 0 / 32 =
        1 - w ^ 2 + w - Real.sqrt (1 - w ^ 2) / 32 -
          (m v).1 ^ 2 + (m v).2 ^ 2)
    (sigma : ℝ) (hsigma : sigma = 1 ∨ sigma = -1)
    (kappa : OpenPartialHomeomorph E2 E2)
    (hkappaSource : closedBall (0 : E2) 2 ⊆ kappa.source)
    (hkappa : ContDiffOn ℝ ∞ kappa kappa.source)
    (hkappaInv : ContDiffOn ℝ ∞ kappa.symm kappa.target)
    (J2 : E2 ≃L[ℝ] (ℝ × ℝ))
    (hJ2 : ∀ x : E2, (J2 x).1 ^ 2 + (J2 x).2 ^ 2 = ‖x‖ ^ 2)
    (u : UnitTwoSphere) (c rho d : ℝ) (hrho : 0 < rho) :
    let h8 := exists_nestedReference_buffered_morse_chart
      w hw_lower hw_upper m hm_point hm_source hm_zero hm hmi hm_height
    let R : ℝ := Classical.choose h8
    let h8R := Classical.choose_spec h8
    let b : ℝ := Classical.choose h8R
    let h8b := Classical.choose_spec h8R
    let e : OpenPartialHomeomorph UnitTwoSphere (ℝ × ℝ) :=
      Classical.choose h8b
    let h8e := Classical.choose_spec h8b
    let P : OpenPartialHomeomorph (ℝ × ℝ) E2 := Classical.choose h8e
    let vstar : E2 := !₂[-Real.sqrt (1 - w ^ 2), 0]
    let pstar : UnitTwoSphere := northSpherePoint ((1 + w)⁻¹ • vstar)
    let k : ℝ := 1 - w ^ 2 + w - Real.sqrt (1 - w ^ 2) / 32
    let rhoN : ℝ := R / 2
    let Lambda : ℝ := rho ^ 2 / rhoN ^ 2
    let sN : E2 → ℝ × ℝ := fun x =>
      (sigma * rhoN * (J2 x).2, sigma * rhoN * (J2 x).1)
    let Q : E2 → ℝ := fun x => (J2 x).1 ^ 2 - (J2 x).2 ^ 2
    let L := heightPlaneCoordinates u
    let R0 := nestedReferenceBallChart d
    ∃ (kref : OpenPartialHomeomorph E2 E2)
      (Gref Gtar : Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
      (A : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞),
    let F := (nestedReferenceDiffeomorph d).trans A
    let B := R0.mapDiffeomorph A
    0 < R ∧ 0 < b ∧ 4 * R ^ 2 < b ∧
    0 < rhoN ∧ 0 < Lambda ∧ Lambda * rhoN ^ 2 = rho ^ 2 ∧
    kref.source = ball (0 : E2) 4 ∧ kref.target = P.target ∧
    (∀ x : E2, kref x = P (sN x)) ∧
    (∀ v : E2, kref.symm v = J2.symm
      (sigma / rhoN * (P.symm v).2, sigma / rhoN * (P.symm v).1)) ∧
    ContDiffOn ℝ ∞ kref kref.source ∧
    ContDiffOn ℝ ∞ kref.symm kref.target ∧
    (∀ x : E2,
      (sN x).1 ^ 2 + (sN x).2 ^ 2 = rhoN ^ 2 * ‖x‖ ^ 2 ∧
      -(sN x).1 ^ 2 + (sN x).2 ^ 2 = rhoN ^ 2 * Q x) ∧
    EqOn Gref kref (closedBall (0 : E2) 2) ∧
    EqOn Gref.symm kref.symm (kref '' closedBall (0 : E2) 2) ∧
    EqOn Gtar kappa (closedBall (0 : E2) 2) ∧
    EqOn Gtar.symm kappa.symm (kappa '' closedBall (0 : E2) 2) ∧
    (∀ X : Set E2, X ⊆ closedBall (0 : E2) 2 →
      Gref '' X = kref '' X ∧ Gtar '' X = kappa '' X) ∧
    (∀ y : E3, A y = L.symm
      (Gtar (Gref.symm (heightCoordinates y).1),
        c + Lambda * ((heightCoordinates y).2 - k - d))) ∧
    (∀ y : E3, A.symm y = heightCoordinates.symm
      (Gref (Gtar.symm (L y).1), k + d + ((L y).2 - c) / Lambda)) ∧
    (∀ y : E3,
      ⟪(u : E3), A y⟫_ℝ = c + Lambda * ((heightCoordinates y).2 - k - d)) ∧
    (∀ y : E3, (heightCoordinates (A.symm y)).2 =
      k + d + (⟪(u : E3), y⟫_ℝ - c) / Lambda) ∧
    ContDiff ℝ ∞ A ∧ ContDiff ℝ ∞ A.symm ∧
    ContDiff ℝ ∞ F ∧ ContDiff ℝ ∞ F.symm ∧
    B.chart = F.toHomeomorph.toOpenPartialHomeomorph ∧
    B.chart.source = univ ∧ B.chart.target = univ ∧
    B.inside = A '' R0.inside ∧
    B.closedRegion = A '' R0.closedRegion ∧
    B.boundary = A '' R0.boundary ∧
    B.boundary = range (fun q : UnitTwoSphere => F (q : E3)) ∧
    (∀ y : E3,
      (y ∈ B.inside ↔ ‖F.symm y‖ < 1) ∧
      (y ∈ B.closedRegion ↔ ‖F.symm y‖ ≤ 1) ∧
      (y ∈ B.boundary ↔ ‖F.symm y‖ = 1)) ∧
    F (pstar : E3) = L.symm (kappa 0, c) ∧
    (∀ x ∈ closedBall (0 : E2) 2,
      (sN x).1 ^ 2 + (sN x).2 ^ 2 ≤ R ^ 2 ∧
      sN x ∈ P.source ∧ sN x ∈ e.target ∧
      e.symm (sN x) ∈ e.source ∧
      F (e.symm (sN x) : E3) = L.symm (kappa x, c + rho ^ 2 * Q x)) ∧
    (∀ x ∈ closedBall (0 : E2) 2, ∀ t : ℝ,
      A.symm (L.symm (kappa x, c + t)) =
        heightCoordinates.symm (P (sN x), k + d + t / Lambda)) ∧
    (∀ x ∈ closedBall (0 : E2) 2, ∀ t : ℝ, |t| < rho ^ 2 →
      |t / Lambda| < b / 16 ∧
      (sN x, k + d + t / Lambda) ∈
        P.source ×ˢ Ioo (k + d - 8 * b) (k + d + 8 * b) ∧
      w / 2 < (heightCoordinates (F.symm (L.symm (kappa x, c + t)))).2 ∧
      (L.symm (kappa x, c + t) ∈ B.inside ↔ t < rho ^ 2 * Q x) ∧
      (L.symm (kappa x, c + t) ∈ B.closedRegion ↔ t ≤ rho ^ 2 * Q x) ∧
      (L.symm (kappa x, c + t) ∈ B.boundary ↔ t = rho ^ 2 * Q x) ∧
      (L.symm (kappa x, c + t) ∉ B.closedRegion ↔ rho ^ 2 * Q x < t)) := by
  classical
  intro h8 R h8R b h8b e h8e P vstar pstar k rhoN Lambda sN Q L R0
  obtain ⟨hR, hb, _hbSmall, hRbudget, _hbHeight, _hpCoordinates,
    hesource, _hetarget, heform, _heinv, hpsource, hepstar, _hesmooth,
    _heismooth, heheight, _hcritical, hPsource, _hPtarget, hbuffer,
    hPform, _hPinv, _hPsubset, _hPzero, hPsm, hPism, hProduct⟩ :=
      Classical.choose_spec h8e
  have hrhoN : 0 < rhoN := half_pos hR
  have hLambda : 0 < Lambda := div_pos (sq_pos_of_pos hrho) (sq_pos_of_pos hrhoN)
  have hScale : Lambda * rhoN ^ 2 = rho ^ 2 := by
    dsimp only [Lambda]
    exact div_mul_cancel₀ _ (sq_pos_of_pos hrhoN).ne'
  have hsigmaSq : sigma ^ 2 = 1 := by
    rcases hsigma with h | h <;> simp only [h] <;> norm_num
  have hcancel (z : ℝ) : sigma / rhoN * (sigma * rhoN * z) = z := by
    calc
      sigma / rhoN * (sigma * rhoN * z) = sigma ^ 2 * z := by
        field_simp [hrhoN.ne']
      _ = z := by rw [hsigmaSq, one_mul]
  have hcancel' (z : ℝ) : sigma * rhoN * (sigma / rhoN * z) = z := by
    calc
      sigma * rhoN * (sigma / rhoN * z) =
          sigma / rhoN * (sigma * rhoN * z) := by ring
      _ = z := hcancel z
  have hsN : ContDiff ℝ ∞ sN :=
    ((contDiff_const (c := sigma * rhoN)).mul
      (contDiff_snd.comp J2.contDiff)).prodMk
      ((contDiff_const (c := sigma * rhoN)).mul (contDiff_fst.comp J2.contDiff))
  let T : Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, ℝ × ℝ) E2 (ℝ × ℝ) ∞ := {
    toFun := sN
    invFun := fun v => J2.symm (sigma / rhoN * v.2, sigma / rhoN * v.1)
    left_inv := by
      intro x
      apply J2.injective
      rw [J2.apply_symm_apply]
      exact Prod.ext (hcancel _) (hcancel _)
    right_inv := by
      intro v
      change sN (J2.symm (sigma / rhoN * v.2, sigma / rhoN * v.1)) = v
      dsimp only [sN]
      rw [J2.apply_symm_apply]
      exact Prod.ext (hcancel' _) (hcancel' _)
    contMDiff_toFun := hsN.contMDiff
    contMDiff_invFun := (J2.symm.contDiff.comp
      (((contDiff_const (c := sigma / rhoN)).mul contDiff_snd).prodMk
        ((contDiff_const (c := sigma / rhoN)).mul contDiff_fst))).contMDiff }
  have hNorm (x : E2) :
      (sN x).1 ^ 2 + (sN x).2 ^ 2 = rhoN ^ 2 * ‖x‖ ^ 2 := by
    dsimp only [sN]
    simp only [mul_pow, hsigmaSq, one_mul]
    calc
      rhoN ^ 2 * (J2 x).2 ^ 2 + rhoN ^ 2 * (J2 x).1 ^ 2 =
          rhoN ^ 2 * ((J2 x).1 ^ 2 + (J2 x).2 ^ 2) := by ring
      _ = rhoN ^ 2 * ‖x‖ ^ 2 := by rw [hJ2]
  have hQuad (x : E2) :
      -(sN x).1 ^ 2 + (sN x).2 ^ 2 = rhoN ^ 2 * Q x := by
    dsimp only [sN, Q]
    simp only [mul_pow, hsigmaSq, one_mul]
    ring
  let kref := T.toHomeomorph.transOpenPartialHomeomorph P
  have hksource : kref.source = ball (0 : E2) 4 := by
    ext x
    change sN x ∈ P.source ↔ x ∈ ball (0 : E2) 4
    rw [hPsource, mem_ofPred_eq, hNorm, mem_ball_zero_iff]
    have hfour : (2 * R) ^ 2 = rhoN ^ 2 * 16 := by dsimp only [rhoN]; ring
    rw [hfour, mul_lt_mul_iff_right₀ (sq_pos_of_pos hrhoN)]
    constructor <;> intro hx <;> nlinarith only [hx, norm_nonneg x]
  have hksm : ContDiffOn ℝ ∞ kref kref.source :=
    hPsm.comp T.contDiff.contDiffOn (fun _ hx => hx)
  have hkism : ContDiffOn ℝ ∞ kref.symm kref.target :=
    T.symm.contDiff.comp_contDiffOn hPism
  have hkclosed : closedBall (0 : E2) 2 ⊆ kref.source := by
    intro x hx
    rw [hksource, mem_ball_zero_iff]
    exact (mem_closedBall_zero_iff.mp hx).trans_lt (by norm_num)
  have extend (K : OpenPartialHomeomorph E2 E2)
      (hsource : closedBall (0 : E2) 2 ⊆ K.source)
      (hK : ContDiffOn ℝ ∞ K K.source)
      (hKi : ContDiffOn ℝ ∞ K.symm K.target) :
      ∃ G : Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞,
        EqOn G K (closedBall (0 : E2) 2) ∧
        EqOn G.symm K.symm (K '' closedBall (0 : E2) 2) := by
    let S2 : Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞ := {
      toFun := fun x => (2 : ℝ) • x
      invFun := fun x => (1 / 2 : ℝ) • x
      left_inv := fun x => by simp only [smul_smul]; norm_num
      right_inv := fun x => by simp only [smul_smul]; norm_num
      contMDiff_toFun := (contDiff_const.smul contDiff_id).contMDiff
      contMDiff_invFun := (contDiff_const.smul contDiff_id).contMDiff }
    let K2 := S2.toHomeomorph.transOpenPartialHomeomorph K
    let B2 : BallNeighborhoodChart E2 E2 := {
      chart := K2
      closedBall_subset_source := by
        intro x hx
        apply hsource
        change (2 : ℝ) • x ∈ closedBall (0 : E2) 2
        rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
          abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
        have hn := mem_closedBall_zero_iff.mp hx
        linarith only [hn]
      smooth := hK.comp S2.contDiff.contDiffOn (fun _ hx => hx)
      smooth_symm := S2.symm.contDiff.comp_contDiffOn hKi }
    obtain ⟨G2, hG2, _, _, _, _⟩ := exists_saddle_planar_ball_chart_extension B2
    let G := S2.symm.trans G2
    have hG : EqOn G K (closedBall (0 : E2) 2) := by
      intro x hx
      have hsmall : S2.symm x ∈ closedBall (0 : E2) 1 := by
        change (1 / 2 : ℝ) • x ∈ closedBall (0 : E2) 1
        rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
          abs_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)]
        have hn := mem_closedBall_zero_iff.mp hx
        linarith only [hn]
      change G2 (S2.symm x) = K x
      rw [hG2 hsmall]
      change K (S2 (S2.symm x)) = K x
      rw [S2.apply_symm_apply]
    refine ⟨G, hG, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    have hix : G.symm (K x) = x := by rw [← hG hx, G.symm_apply_apply]
    exact hix.trans (K.left_inv (hsource hx)).symm
  obtain ⟨Gref, hGref, hGrefInv⟩ := extend kref hkclosed hksm hkism
  obtain ⟨Gtar, hGtar, hGtarInv⟩ := extend kappa hkappaSource hkappa hkappaInv
  have hGrP (x : E2) (hx : x ∈ closedBall (0 : E2) 2) :
      Gref x = P (sN x) := hGref hx
  have hImages (X : Set E2) (hX : X ⊆ closedBall (0 : E2) 2) :
      Gref '' X = kref '' X ∧ Gtar '' X = kappa '' X :=
    ⟨image_congr (fun _ hx => hGref (hX hx)),
      image_congr (fun _ hx => hGtar (hX hx))⟩
  let fA : E3 → E3 := fun y => L.symm
    (Gtar (Gref.symm (heightCoordinates y).1),
      c + Lambda * ((heightCoordinates y).2 - k - d))
  let gA : E3 → E3 := fun y => heightCoordinates.symm
    (Gref (Gtar.symm (L y).1), k + d + ((L y).2 - c) / Lambda)
  have hfA : ContDiff ℝ ∞ fA := L.symm.contDiff.comp
    ((Gtar.contDiff.comp (Gref.symm.contDiff.comp
      (contDiff_fst.comp heightCoordinates.contDiff))).prodMk
      (contDiff_const.add (contDiff_const.mul
        (((contDiff_snd.comp heightCoordinates.contDiff).sub contDiff_const).sub
          contDiff_const))))
  have hgA : ContDiff ℝ ∞ gA := heightCoordinates.symm.contDiff.comp
    ((Gref.contDiff.comp (Gtar.symm.contDiff.comp (contDiff_fst.comp L.contDiff))).prodMk
      (contDiff_const.add (((contDiff_snd.comp L.contDiff).sub contDiff_const).div_const
        Lambda)))
  let A : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞ := {
    toFun := fA
    invFun := gA
    left_inv := by
      intro y
      apply heightCoordinates.injective
      dsimp only [fA, gA]
      rw [L.apply_symm_apply, heightCoordinates.apply_symm_apply,
        Gtar.symm_apply_apply, Gref.apply_symm_apply]
      apply Prod.ext
      · rfl
      · dsimp only
        field_simp [hLambda.ne']
        ring
    right_inv := by
      intro y
      apply L.injective
      dsimp only [fA, gA]
      rw [heightCoordinates.apply_symm_apply, L.apply_symm_apply,
        Gref.symm_apply_apply, Gtar.apply_symm_apply]
      apply Prod.ext
      · rfl
      · dsimp only
        field_simp [hLambda.ne']
        ring
    contMDiff_toFun := hfA.contMDiff
    contMDiff_invFun := hgA.contMDiff }
  have hAp (y : E3) : A y = L.symm
      (Gtar (Gref.symm (heightCoordinates y).1),
        c + Lambda * ((heightCoordinates y).2 - k - d)) := rfl
  have hAi (y : E3) : A.symm y = heightCoordinates.symm
      (Gref (Gtar.symm (L y).1), k + d + ((L y).2 - c) / Lambda) := rfl
  have hHeight (y : E3) :
      ⟪(u : E3), A y⟫_ℝ = c + Lambda * ((heightCoordinates y).2 - k - d) := by
    rw [← heightPlaneCoordinates_snd u (A y)]
    change (L (A y)).2 = _
    rw [hAp, L.apply_symm_apply]
  have hHeightInv (y : E3) : (heightCoordinates (A.symm y)).2 =
      k + d + (⟪(u : E3), y⟫_ℝ - c) / Lambda := by
    rw [hAi, heightCoordinates.apply_symm_apply]
    dsimp only
    rw [heightPlaneCoordinates_snd]
  let F := (nestedReferenceDiffeomorph d).trans A
  let B := R0.mapDiffeomorph A
  have hBs : B.chart.source = univ := by
    ext y
    constructor
    · intro _; exact mem_univ y
    · intro _; exact ⟨mem_univ y, mem_univ _⟩
  have hBt : B.chart.target = univ := by
    ext y
    constructor
    · intro _; exact mem_univ y
    · intro _; exact ⟨mem_univ y, mem_univ _⟩
  have hBchart : B.chart = F.toHomeomorph.toOpenPartialHomeomorph := by
    apply OpenPartialHomeomorph.ext
    · intro y; rfl
    · intro y; rfl
    · exact hBs
  have hBi : B.inside = A '' R0.inside := R0.mapDiffeomorph_inside A
  have hBc : B.closedRegion = A '' R0.closedRegion := R0.mapDiffeomorph_closedRegion A
  have hBb : B.boundary = A '' R0.boundary := R0.mapDiffeomorph_boundary A
  have hBoundary : B.boundary = range (fun q : UnitTwoSphere => F (q : E3)) := by
    change F '' sphere (0 : E3) 1 = _
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨q, rfl⟩
      exact ⟨q, q.property, rfl⟩
  have himage (X : Set E3) (y : E3) : y ∈ A '' X ↔ A.symm y ∈ X := by
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa only [A.symm_apply_apply] using hx
    · intro hy
      exact ⟨A.symm y, hy, A.apply_symm_apply y⟩
  have hFimage (X : Set E3) (y : E3) : y ∈ F '' X ↔ F.symm y ∈ X := by
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa only [F.symm_apply_apply] using hx
    · intro hy
      exact ⟨F.symm y, hy, F.apply_symm_apply y⟩
  have hRegions (y : E3) :
      (y ∈ B.inside ↔ ‖F.symm y‖ < 1) ∧
      (y ∈ B.closedRegion ↔ ‖F.symm y‖ ≤ 1) ∧
      (y ∈ B.boundary ↔ ‖F.symm y‖ = 1) := by
    change (y ∈ F '' ball 0 1 ↔ _) ∧
      (y ∈ F '' closedBall 0 1 ↔ _) ∧ (y ∈ F '' sphere 0 1 ↔ _)
    simp only [hFimage, mem_ball_zero_iff, mem_closedBall_zero_iff,
      mem_sphere_zero_iff_norm, and_self]
  have hBound (x : E2) (hx : x ∈ closedBall (0 : E2) 2) :
      (sN x).1 ^ 2 + (sN x).2 ^ 2 ≤ R ^ 2 := by
    have hn := mem_closedBall_zero_iff.mp hx
    have hnSq : ‖x‖ ^ 2 ≤ 4 := by nlinarith only [hn, norm_nonneg x]
    rw [hNorm]
    calc
      rhoN ^ 2 * ‖x‖ ^ 2 ≤ rhoN ^ 2 * 4 :=
        mul_le_mul_of_nonneg_left hnSq (sq_nonneg rhoN)
      _ = R ^ 2 := by dsimp only [rhoN]; ring
  have hRadial (x : E2) (hx : x ∈ closedBall (0 : E2) 2) :
      sN x ∈ P.source ∧ sN x ∈ e.target := by
    have hsmall : (sN x).1 ^ 2 + (sN x).2 ^ 2 < (2 * R) ^ 2 :=
      (hBound x hx).trans_lt (by nlinarith only [sq_pos_of_pos hR])
    exact ⟨hPsource.symm ▸ hsmall, hbuffer hsmall.le⟩
  have hNativeFst (y : E3) :
      (heightCoordinates (nestedReferenceDiffeomorph d y)).1 =
        (heightCoordinates y).1 := by
    ext i
    fin_cases i <;> rfl
  have hPoint (x : E2) (hx : x ∈ closedBall (0 : E2) 2) :
      F (e.symm (sN x) : E3) = L.symm (kappa x, c + rho ^ 2 * Q x) := by
    have hes := (hRadial x hx).2
    have hqs := e.map_target hes
    have hms : (heightCoordinates (e.symm (sN x) : E3)).1 ∈ m.source := by
      rw [hesource] at hqs
      exact hqs.2
    have hHorizontal : (heightCoordinates (e.symm (sN x) : E3)).1 = P (sN x) := by
      calc
        (heightCoordinates (e.symm (sN x) : E3)).1 =
            m.symm (m (heightCoordinates (e.symm (sN x) : E3)).1) :=
          (m.left_inv hms).symm
        _ = m.symm (e (e.symm (sN x))) := by rw [heform]
        _ = m.symm (sN x) := by rw [e.right_inv hes]
        _ = P (sN x) := (hPform _).symm
    have hNativeCoordinates :
        heightCoordinates (nestedReferenceDiffeomorph d (e.symm (sN x) : E3)) =
          (P (sN x), k + d + rhoN ^ 2 * Q x) := by
      apply Prod.ext
      · exact (hNativeFst _).trans hHorizontal
      · rw [heheight d _ hqs, e.right_inv hes]
        have hq := hQuad x
        change k + d - (sN x).1 ^ 2 + (sN x).2 ^ 2 = k + d + rhoN ^ 2 * Q x
        linarith only [hq]
    change A (nestedReferenceDiffeomorph d (e.symm (sN x) : E3)) = _
    rw [hAp, hNativeCoordinates]
    dsimp only
    rw [← hGrP x hx, Gref.symm_apply_apply, hGtar hx]
    apply congrArg L.symm
    apply Prod.ext
    · rfl
    · dsimp only
      calc
        c + Lambda * (k + d + rhoN ^ 2 * Q x - k - d) =
            c + (Lambda * rhoN ^ 2) * Q x := by ring
        _ = c + rho ^ 2 * Q x := by rw [hScale]
  have hCenter : F (pstar : E3) = L.symm (kappa 0, c) := by
    have hs0 : sN 0 = 0 := by simp only [sN, map_zero, mul_zero, Prod.zero_eq_mk]
    have he0 : e.symm (0 : ℝ × ℝ) = pstar := by
      rw [← hepstar]
      exact e.left_inv hpsource
    have hq0 : Q 0 = 0 := by simp only [Q, map_zero, sub_self, Prod.fst_zero, Prod.snd_zero]
    simpa only [hs0, he0, hq0, mul_zero, add_zero] using hPoint 0 (by simp)
  have hLocal (x : E2) (hx : x ∈ closedBall (0 : E2) 2) (t : ℝ) :
      A.symm (L.symm (kappa x, c + t)) =
        heightCoordinates.symm (P (sN x), k + d + t / Lambda) := by
    rw [hAi, L.apply_symm_apply]
    dsimp only
    rw [← hGtar hx, Gtar.symm_apply_apply, hGrP x hx]
    congr 2
    ring
  have hTime (t : ℝ) (ht : |t| < rho ^ 2) : |t / Lambda| < b / 16 := by
    rw [abs_div, abs_of_pos hLambda]
    calc
      |t| / Lambda < rho ^ 2 / Lambda := div_lt_div_of_pos_right ht hLambda
      _ = rhoN ^ 2 := (div_eq_iff hLambda.ne').mpr (by nlinarith only [hScale])
      _ < b / 16 := by dsimp only [rhoN]; nlinarith only [hRbudget]
  have hMulQ (x : E2) : Lambda * (rhoN ^ 2 * Q x) = rho ^ 2 * Q x := by
    rw [← mul_assoc, hScale]
  obtain ⟨C8, hCsource, _hCtarget, _hCsm, _hCism, _hCzero, _hCbuffer,
    _hCgraph, _hCinv, hCform⟩ := hProduct (k + d)
  have hshift : k + d - (1 - w ^ 2 + w - Real.sqrt (1 - w ^ 2) / 32) = d := by
    dsimp only [k]
    ring
  have hBox (x : E2) (hx : x ∈ closedBall (0 : E2) 2) (t : ℝ)
      (ht : |t| < rho ^ 2) :
      |t / Lambda| < b / 16 ∧
      (sN x, k + d + t / Lambda) ∈
        P.source ×ˢ Ioo (k + d - 8 * b) (k + d + 8 * b) ∧
      w / 2 < (heightCoordinates (F.symm (L.symm (kappa x, c + t)))).2 ∧
      (L.symm (kappa x, c + t) ∈ B.inside ↔ t < rho ^ 2 * Q x) ∧
      (L.symm (kappa x, c + t) ∈ B.closedRegion ↔ t ≤ rho ^ 2 * Q x) ∧
      (L.symm (kappa x, c + t) ∈ B.boundary ↔ t = rho ^ 2 * Q x) ∧
      (L.symm (kappa x, c + t) ∉ B.closedRegion ↔ rho ^ 2 * Q x < t) := by
    have htime := hTime t ht
    have h8time : |t / Lambda| < 8 * b := by linarith only [htime, hb]
    have hguard : (sN x, k + d + t / Lambda) ∈
        P.source ×ˢ Ioo (k + d - 8 * b) (k + d + 8 * b) := by
      refine ⟨(hRadial x hx).1, ?_⟩
      obtain ⟨hl, hu⟩ := abs_lt.mp h8time
      constructor <;> linarith only [hl, hu]
    have hCguard : (sN x, k + d + t / Lambda) ∈ C8.source := by
      rw [hCsource]
      exact ⟨hPsource ▸ hguard.1, hguard.2⟩
    obtain ⟨hform, _hheight, hpos, hbd, hcl, hin, hout⟩ :=
      hCform (sN x, k + d + t / Lambda) hCguard
    have hCvalue : C8 (sN x, k + d + t / Lambda) =
        A.symm (L.symm (kappa x, c + t)) := hform.trans (hLocal x hx t).symm
    rw [hCvalue] at hpos hbd hcl hin hout
    rw [hshift] at hpos hbd hcl hin hout
    have hlevel : k + d - (sN x).1 ^ 2 + (sN x).2 ^ 2 =
        k + d + rhoN ^ 2 * Q x := by
      have hq := hQuad x
      linarith only [hq]
    have hlt : k + d + t / Lambda < k + d - (sN x).1 ^ 2 + (sN x).2 ^ 2 ↔
        t < rho ^ 2 * Q x := by
      rw [hlevel, add_lt_add_iff_left, div_lt_iff₀ hLambda,
        mul_comm (rhoN ^ 2 * Q x) Lambda, hMulQ]
    have hle : k + d + t / Lambda ≤ k + d - (sN x).1 ^ 2 + (sN x).2 ^ 2 ↔
        t ≤ rho ^ 2 * Q x := by
      rw [hlevel, add_le_add_iff_left, div_le_iff₀ hLambda,
        mul_comm (rhoN ^ 2 * Q x) Lambda, hMulQ]
    have heq : k + d + t / Lambda = k + d - (sN x).1 ^ 2 + (sN x).2 ^ 2 ↔
        t = rho ^ 2 * Q x := by
      rw [hlevel, add_right_inj, div_eq_iff hLambda.ne',
        mul_comm (rhoN ^ 2 * Q x) Lambda, hMulQ]
    have hgt : k + d - (sN x).1 ^ 2 + (sN x).2 ^ 2 < k + d + t / Lambda ↔
        rho ^ 2 * Q x < t := by
      rw [hlevel, add_lt_add_iff_left, lt_div_iff₀ hLambda,
        mul_comm (rhoN ^ 2 * Q x) Lambda, hMulQ]
    refine ⟨htime, hguard, hpos, ?_, ?_, ?_, ?_⟩
    · rw [hBi, himage]
      exact hin.trans hlt
    · rw [hBc, himage]
      exact hcl.trans hle
    · rw [hBb, himage]
      exact hbd.trans heq
    · rw [hBc, himage]
      exact hout.trans hgt
  exact ⟨kref, Gref, Gtar, A, hR, hb, hRbudget, hrhoN, hLambda, hScale,
    hksource, rfl, fun _ => rfl, fun _ => rfl, hksm, hkism,
    fun x => ⟨hNorm x, hQuad x⟩, hGref, hGrefInv, hGtar, hGtarInv, hImages,
    hAp, hAi, hHeight, hHeightInv, A.contDiff, A.symm.contDiff,
    F.contDiff, F.symm.contDiff, hBchart, hBs, hBt, hBi, hBc, hBb,
    hBoundary, hRegions, hCenter,
    fun x hx => ⟨hBound x hx, (hRadial x hx).1, (hRadial x hx).2,
      e.map_target (hRadial x hx).2, hPoint x hx⟩, hLocal, hBox⟩

end PoincareConjecture.M25.Topology3D.NestedReferenceLower
