import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOneShellCoordinates
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOneShellBoundary
import PoincareConjecture.Proofs.M76.Mathlib.SquareAnnulusOpenChart
import PoincareConjecture.Proofs.M76.Mathlib.HamiltonHandleCubeBall
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLProduct
import PoincareConjecture.Proofs.M76.Mathlib.CompactLocallyPLComposition

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "W" => (ℝ × (ℝ × ℝ))
local notation "Q" => sphere (0 : V2) 1
local notation "I" => Icc (-(1 / 4 : ℝ)) (1 / 4)

noncomputable def standardMeridianBandMap (p : V2 × ℝ) : W :=
  (p.1 0, -((7 / 4 : ℝ), (7 / 4 : ℝ)) +
    PLAnnularStrip.annulusMap (7 / 2) (by norm_num)
      (((p.2 : ℝ) : AddCircle (4 * (7 / 2 : ℝ))), -p.1 1 / 4))

private theorem exists_marked_angular_chart :
    ∃ P : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ),
      P.source = Ioo (-7) 7 ×ˢ Ioo (-(1 / 2)) (1 / 2) ∧
      P ∈ piecewiseAffineGroupoid (ℝ × ℝ) ∧
      (∀ p : ℝ × ℝ, P p = -((7 / 4 : ℝ), (7 / 4 : ℝ)) +
        PLAnnularStrip.annulusMap (7 / 2) (by norm_num)
          (((p.1 : ℝ) : AddCircle (4 * (7 / 2 : ℝ))), p.2)) ∧
      (∀ p ∈ P.source, ‖P p‖ = 7 / 4 - p.2) ∧
      ∀ t ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2), P (0, t) = (t - 7 / 4, t - 7 / 4) := by
  let : Fact (0 < 4 * (7 / 2 : ℝ)) := ⟨by norm_num⟩
  obtain ⟨e, heS, heval, hePL⟩ := PLAnnularStrip.exists_annulus_PL_openPartialHomeomorph
    (by norm_num : (0 : ℝ) < 7 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : 4 * (1 / 2 : ℝ) < 7 / 2)
  let C := (AddCircle.openPartialHomeomorphCoe (4 * (7 / 2 : ℝ)) (-7)).prod
    (OpenPartialHomeomorph.refl ℝ)
  let a : (ℝ × ℝ) ≃ᴬ[ℝ] (ℝ × ℝ) :=
    ContinuousAffineEquiv.constVAdd ℝ (ℝ × ℝ) (-((7 / 4 : ℝ), (7 / 4 : ℝ)))
  let P := (C.trans e).transHomeomorph a.toHomeomorph
  have hsource : P.source = Ioo (-7) 7 ×ˢ Ioo (-(1 / 2)) (1 / 2) := by
    ext p
    change (p ∈ C.source ∧ C p ∈ e.source) ↔ _
    rw [heS]
    change ((p.1 ∈ Ioo (-7) (-7 + 4 * (7 / 2 : ℝ)) ∧ p.2 ∈ univ) ∧
      (C p).1 ∈ univ ∧ p.2 ∈ Ioo (-(1 / 2)) (1 / 2)) ↔ _
    norm_num
  have hPL : P ∈ piecewiseAffineGroupoid (ℝ × ℝ) := by
    apply (mem_piecewiseAffineGroupoid_iff_forward P).mpr
    have h := (locallyPiecewiseAffineOn_affine a.toContinuousAffineMap isOpen_univ).comp
      (hePL (-7)).1
    change LocallyPiecewiseAffineOn (fun x => a (e (C x))) (C.trans e).source
    simpa only [preimage_univ, inter_univ, Function.comp_def,
      ContinuousAffineEquiv.coe_toContinuousAffineMap,
      OpenPartialHomeomorph.trans_apply] using h
  have hval (p : ℝ × ℝ) : P p = a
      (PLAnnularStrip.annulusMap (7 / 2) (by norm_num)
        ((p.1 : AddCircle (4 * (7 / 2 : ℝ))), p.2)) := by
    change a (e (C p)) = _
    rw [heval]
    rfl
  have hwidth {t : ℝ} (ht : t ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2)) :
      4 * |t| < (7 / 2 : ℝ) := by
    have h := abs_lt.mpr ht
    linarith
  refine ⟨P, hsource, hPL, fun p => hval p, ?_, ?_⟩
  · intro p hp
    have ht : p.2 ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2) := (hsource ▸ hp).2
    have hd := PLAnnularStrip.depth_annulusMap (by norm_num : (0 : ℝ) < 7 / 2)
      (hwidth ht) (p.1 : AddCircle (4 * (7 / 2 : ℝ)))
    have hpadd : P p + ((7 / 4 : ℝ), (7 / 4 : ℝ)) =
        PLAnnularStrip.annulusMap (7 / 2) (by norm_num)
          ((p.1 : AddCircle (4 * (7 / 2 : ℝ))), p.2) := by
      rw [hval]
      change -((7 / 4 : ℝ), (7 / 4 : ℝ)) + _ + _ = _
      abel
    rw [← hpadd, depth_centered] at hd
    linarith
  · intro t ht
    rw [hval]
    rw [PLAnnularStrip.annulusMap_coe (by norm_num : (0 : ℝ) < 7 / 2)
      (hwidth ht) (by norm_num : (0 : ℝ) ∈ Icc 0 (4 * (7 / 2)))]
    have hb := PLAnnularStrip.wrappedStripMap_block (hwidth ht)
      (by norm_num : (0 : ℝ) ∈ Icc 0 (7 / 2)) (0 : Fin 4)
    simp only [Fin.val_zero, Nat.cast_zero, zero_mul, zero_add] at hb
    rw [hb]
    change (- (7 / 4 : ℝ) + PLAnnularStrip.coordinate (7 / 2) 0 t,
      - (7 / 4 : ℝ) + t) = _
    rw [(PLAnnularStrip.coordinate_endpoints (hwidth ht)).1]
    apply Prod.ext <;> ring

private noncomputable def meridianCoordinates : (V2 × ℝ) ≃ₗ[ℝ] W where
  toFun p := (p.1 0, (p.2, -p.1 1 / 4))
  invFun p := (![p.1, -4 * p.2.2], p.2.1)
  left_inv p := by
    apply Prod.ext
    · ext i
      fin_cases i
      · rfl
      · change -4 * (-p.1 1 / 4) = p.1 1
        ring
    · rfl
  right_inv p := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · change -(-4 * p.2.2) / 4 = p.2.2
        ring
  map_add' p q := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · change -(p.1 1 + q.1 1) / 4 = -p.1 1 / 4 + -q.1 1 / 4
        ring
  map_smul' a p := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · change -(a * p.1 1) / 4 = a * (-p.1 1 / 4)
        ring

private theorem exists_standard_meridian_band_with_formula :
    ∃ F : (V2 × ℝ) → W, F = standardMeridianBandMap ∧
      FinitePiecewiseAffineOn F (Q ×ˢ I) ∧ InjOn F (Q ×ˢ I) ∧
      MapsTo F (Q ×ˢ I) (frontier squareShell) ∧
      (∀ x : Q, F ((x : V2), 0) =
        ((x : V2) 0, (-(((x : V2) 1 + 7) / 4), -(((x : V2) 1 + 7) / 4)))) ∧
      IsOpen ((Subtype.val : frontier squareShell → W) ⁻¹'
        (F '' (Q ×ˢ Ioo (-(1 / 4 : ℝ)) (1 / 4)))) := by
  obtain ⟨P, hPS, hPPL, hformula, hnorm, hzero⟩ := exists_marked_angular_chart
  let a := meridianCoordinates.toContinuousLinearEquiv.toContinuousAffineEquiv
  let H := a.toHomeomorph.toOpenPartialHomeomorph.trans ((OpenPartialHomeomorph.refl ℝ).prod P)
  have hHval (p : V2 × ℝ) : H p = (p.1 0, P (p.2, -p.1 1 / 4)) := rfl
  have hbounds (x : Q) (i : Fin 2) : |(x : V2) i| ≤ 1 := by
    have h := norm_le_pi_norm (x : V2) i
    simpa only [Real.norm_eq_abs, mem_sphere_zero_iff_norm.mp x.property] using h
  have hsource : Q ×ˢ I ⊆ H.source := by
    intro p hp
    refine ⟨mem_univ _, mem_univ _, ?_⟩
    change (p.2, -p.1 1 / 4) ∈ P.source
    rw [hPS]
    have hb := abs_le.mp (hbounds ⟨p.1, hp.1⟩ 1)
    change -1 ≤ p.1 1 ∧ p.1 1 ≤ 1 at hb
    change (-7 < p.2 ∧ p.2 < 7) ∧ -(1 / 2 : ℝ) < -p.1 1 / 4 ∧
      -p.1 1 / 4 < 1 / 2
    exact ⟨⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩,
      ⟨by linarith [hb.1, hb.2], by linarith [hb.1, hb.2]⟩⟩
  let C : Set (V2 × ℝ) := closedBall (0 : V2) 1 ×ˢ univ
  have himage : H.IsImage C squareShell := by
    intro p hp
    have hn := hnorm (p.2, -p.1 1 / 4) hp.2.2
    change ‖P (p.2, -p.1 1 / 4)‖ = 7 / 4 - (-p.1 1 / 4) at hn
    constructor
    · intro hm
      have hs : p.1 0 ∈ Icc (-1 : ℝ) 1 := hm.1
      have hr : ‖P (p.2, -p.1 1 / 4)‖ ∈ Icc (3 / 2 : ℝ) 2 := hm.2
      refine ⟨mem_closedBall_zero_iff.mpr ?_, mem_univ _⟩
      rw [pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)]
      intro i
      rw [Real.norm_eq_abs, abs_le]
      fin_cases i
      · exact hs
      · change -1 ≤ p.1 1 ∧ p.1 1 ≤ 1
        constructor <;> linarith [hr.1, hr.2]
    · intro hm
      have hb := (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mp
        (mem_closedBall_zero_iff.mp hm.1)
      have h0 : |p.1 0| ≤ 1 := by simpa only [Real.norm_eq_abs] using hb 0
      have h1 := abs_le.mp (show |p.1 1| ≤ 1 by simpa only [Real.norm_eq_abs] using hb 1)
      refine ⟨abs_le.mp h0, ?_⟩
      change ‖P (p.2, -p.1 1 / 4)‖ ∈ Icc (3 / 2 : ℝ) 2
      constructor <;> linarith [h1.1, h1.2]
  have hfront : H.IsImage (Q ×ˢ (univ : Set ℝ)) (frontier squareShell) := by
    simpa only [C, frontier_prod_univ_eq, frontier_closedBall _ one_ne_zero] using himage.frontier
  have hPL : LocallyPiecewiseAffineOn H H.source := by
    exact ((locallyPiecewiseAffineOn_affine (ContinuousAffineMap.id ℝ ℝ) isOpen_univ).prodMap
      hPPL.1).comp (locallyPiecewiseAffineOn_affine a.toContinuousAffineMap isOpen_univ)
  have hqPL : FinitePiecewiseAffineOn (id : V2 → V2) Q := by
    obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ :=
      isFinitePLBallPair_unit_cube (ι := Fin 2)
    let J := K.frontierSubcomplex (closedBall (0 : V2) 1)
    have hJ := K.frontierSubcomplex_finite (closedBall (0 : V2) 1) hK
    have hJs := K.frontierSubcomplex_space isClosed_closedBall (convex_closedBall _ _)
      ⟨0, ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩ hKs
    rw [frontier_closedBall _ one_ne_zero] at hJs
    exact ⟨J, hJ, hJs, J.affineOnFaces_affine (ContinuousAffineMap.id ℝ V2)⟩
  have hiPL : FinitePiecewiseAffineOn (id : ℝ → ℝ) I := by
    obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ :=
      isFinitePLBallPair_Icc (by norm_num : -(1 / 4 : ℝ) < 1 / 4)
    exact ⟨K, hK, hKs, K.affineOnFaces_affine (ContinuousAffineMap.id ℝ ℝ)⟩
  obtain ⟨K, hK, hKs, _⟩ := hqPL.prodMap hiPL
  have hFPL : FinitePiecewiseAffineOn H (Q ×ˢ I) := by
    rw [← hKs]
    exact hPL.finitePiecewiseAffineOn K hK (hKs ▸ hsource)
  have hformulaH : (H : V2 × ℝ → W) = standardMeridianBandMap := by
    funext p
    rw [hHval, hformula]
    rfl
  refine ⟨H, hformulaH, hFPL, H.injOn.mono hsource, ?_, ?_, ?_⟩
  · intro p hp
    exact (hfront.apply_mem_iff (hsource hp)).mpr ⟨hp.1, mem_univ _⟩
  · intro x
    rw [hHval, hzero]
    · apply Prod.ext
      · rfl
      · apply Prod.ext <;> ring
    · have hb := abs_le.mp (hbounds x 1)
      constructor <;> linarith [hb.1, hb.2]
  · let U : Set W := H.target ∩ H.symm ⁻¹' (univ ×ˢ Ioo (-(1 / 4 : ℝ)) (1 / 4))
    have hU : IsOpen U := H.isOpen_inter_preimage_symm (isOpen_univ.prod isOpen_Ioo)
    have heq : H '' (Q ×ˢ Ioo (-(1 / 4 : ℝ)) (1 / 4)) = frontier squareShell ∩ U := by
      ext y
      constructor
      · rintro ⟨p, hp, rfl⟩
        have hpS := hsource ⟨hp.1, Ioo_subset_Icc_self hp.2⟩
        refine ⟨(hfront.apply_mem_iff hpS).mpr ⟨hp.1, mem_univ _⟩,
          H.map_source hpS, ?_⟩
        change H.symm (H p) ∈ univ ×ˢ Ioo (-(1 / 4 : ℝ)) (1 / 4)
        rw [H.left_inv hpS]
        exact ⟨mem_univ _, hp.2⟩
      · rintro ⟨hyf, hyT, hyw⟩
        have hpS := H.map_target hyT
        have hpq := (hfront.apply_mem_iff hpS).mp (by rwa [H.right_inv hyT])
        exact ⟨H.symm y, ⟨hpq.1, hyw.2⟩, H.right_inv hyT⟩
    have heq' : (Subtype.val : frontier squareShell → W) ⁻¹'
        (H '' (Q ×ˢ Ioo (-(1 / 4 : ℝ)) (1 / 4))) =
        (Subtype.val : frontier squareShell → W) ⁻¹' U := by
      ext y
      rw [heq]
      exact and_iff_right y.property
    rw [heq']
    exact hU.preimage continuous_subtype_val

theorem standardMeridianBandMap_properties :
    FinitePiecewiseAffineOn standardMeridianBandMap (Q ×ˢ I) ∧
      InjOn standardMeridianBandMap (Q ×ˢ I) ∧
      MapsTo standardMeridianBandMap (Q ×ˢ I) (frontier squareShell) ∧
      (∀ x : Q, standardMeridianBandMap ((x : V2), 0) =
        ((x : V2) 0, (-(((x : V2) 1 + 7) / 4), -(((x : V2) 1 + 7) / 4)))) ∧
      IsOpen ((Subtype.val : frontier squareShell → W) ⁻¹'
        (standardMeridianBandMap '' (Q ×ˢ Ioo (-(1 / 4 : ℝ)) (1 / 4)))) := by
  obtain ⟨F, rfl, hPL, hinj, hmap, hzero, hopen⟩ :=
    exists_standard_meridian_band_with_formula
  exact ⟨hPL, hinj, hmap, hzero, hopen⟩

theorem exists_standard_meridian_band :
    ∃ F : (V2 × ℝ) → W, FinitePiecewiseAffineOn F (Q ×ˢ I) ∧ InjOn F (Q ×ˢ I) ∧
      MapsTo F (Q ×ˢ I) (frontier squareShell) ∧
      (∀ x : Q, F ((x : V2), 0) =
        ((x : V2) 0, (-(((x : V2) 1 + 7) / 4), -(((x : V2) 1 + 7) / 4)))) ∧
      IsOpen ((Subtype.val : frontier squareShell → W) ⁻¹'
        (F '' (Q ×ˢ Ioo (-(1 / 4 : ℝ)) (1 / 4)))) :=
  ⟨standardMeridianBandMap, standardMeridianBandMap_properties⟩

theorem exists_standard_meridian_ambient_chart :
    ∃ H : OpenPartialHomeomorph (V2 × ℝ) W,
      (H : (V2 × ℝ) → W) = standardMeridianBandMap ∧
      closedBall (0 : V2) 1 ×ˢ I ⊆ H.source ∧
      LocallyPiecewiseAffineOn H H.source ∧
      H.IsImage (closedBall (0 : V2) 1 ×ˢ (univ : Set ℝ)) squareShell ∧
      ∀ x ∈ closedBall (0 : V2) 1, H (x, 0) =
        (x 0, (-((x 1 + 7) / 4), -((x 1 + 7) / 4))) := by
  obtain ⟨P, hPS, hPPL, hformula, hnorm, hzero⟩ := exists_marked_angular_chart
  let a := meridianCoordinates.toContinuousLinearEquiv.toContinuousAffineEquiv
  let H := a.toHomeomorph.toOpenPartialHomeomorph.trans
    ((OpenPartialHomeomorph.refl ℝ).prod P)
  have hHval (p : V2 × ℝ) : H p = (p.1 0, P (p.2, -p.1 1 / 4)) := rfl
  have hbounds {x : V2} (hx : x ∈ closedBall (0 : V2) 1) (i : Fin 2) :
      |x i| ≤ 1 := by
    have h := (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mp
      (mem_closedBall_zero_iff.mp hx) i
    simpa only [Real.norm_eq_abs] using h
  have hsource : closedBall (0 : V2) 1 ×ˢ I ⊆ H.source := by
    intro p hp
    refine ⟨mem_univ _, mem_univ _, ?_⟩
    change (p.2, -p.1 1 / 4) ∈ P.source
    rw [hPS]
    have hb := abs_le.mp (hbounds hp.1 1)
    change (-7 < p.2 ∧ p.2 < 7) ∧ -(1 / 2 : ℝ) < -p.1 1 / 4 ∧
      -p.1 1 / 4 < 1 / 2
    exact ⟨⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩,
      ⟨by linarith [hb.1, hb.2], by linarith [hb.1, hb.2]⟩⟩
  have himage : H.IsImage (closedBall (0 : V2) 1 ×ˢ (univ : Set ℝ)) squareShell := by
    intro p hp
    have hn := hnorm (p.2, -p.1 1 / 4) hp.2.2
    change ‖P (p.2, -p.1 1 / 4)‖ = 7 / 4 - (-p.1 1 / 4) at hn
    constructor
    · intro hm
      have hs : p.1 0 ∈ Icc (-1 : ℝ) 1 := hm.1
      have hr : ‖P (p.2, -p.1 1 / 4)‖ ∈ Icc (3 / 2 : ℝ) 2 := hm.2
      refine ⟨mem_closedBall_zero_iff.mpr ?_, mem_univ _⟩
      rw [pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)]
      intro i
      rw [Real.norm_eq_abs, abs_le]
      fin_cases i
      · exact hs
      · change -1 ≤ p.1 1 ∧ p.1 1 ≤ 1
        constructor <;> linarith [hr.1, hr.2]
    · intro hm
      have h0 := abs_le.mp (hbounds hm.1 0)
      have h1 := abs_le.mp (hbounds hm.1 1)
      refine ⟨h0, ?_⟩
      change ‖P (p.2, -p.1 1 / 4)‖ ∈ Icc (3 / 2 : ℝ) 2
      constructor <;> linarith [h1.1, h1.2]
  have hPL : LocallyPiecewiseAffineOn H H.source := by
    exact ((locallyPiecewiseAffineOn_affine (ContinuousAffineMap.id ℝ ℝ) isOpen_univ).prodMap
      hPPL.1).comp (locallyPiecewiseAffineOn_affine a.toContinuousAffineMap isOpen_univ)
  refine ⟨H, ?_, hsource, hPL, himage, ?_⟩
  · funext p
    rw [hHval, hformula]
    rfl
  · intro x hx
    rw [hHval, hzero]
    · apply Prod.ext
      · rfl
      · apply Prod.ext <;> ring
    · have hb := abs_le.mp (hbounds hx 1)
      constructor <;> linarith [hb.1, hb.2]

end PoincareConjecture.M76.HamiltonIndexOne
