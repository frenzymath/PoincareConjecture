import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.CommonMiddleClockData
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.CommonMiddleExterior
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NativeProjectedFields
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.PlanarFamilyHeightLift
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

set_option autoImplicit false

open Set Metric
open scoped ContDiff NNReal Manifold InnerProductSpace Matrix

namespace PoincareConjecture.M25.Topology3D

local notation "D2" => Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞
local notation "D3" => Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞

set_option linter.unusedVariables false in

theorem exists_saddle_common_middle_isotopy
    (u : UnitTwoSphere) (c rho delta : ℝ)
    (hrho : 0 < rho) (hdelta : 0 < delta)
    (hsmall : delta ≤ rho ^ 2 / 128)
    (J2 : E2 ≃L[ℝ] (ℝ × ℝ))
    (hJ2 : ∀ x : E2, (J2 x).1 ^ 2 + (J2 x).2 ^ 2 = ‖x‖ ^ 2)
    (gRef : Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
    (X : Fin 2 → E3 → E3)
    (hX : ∀ j : Fin 2, ContDiff ℝ ∞ (X j))
    (S : Fin 2 → Set E3) (hS : ∀ j : Fin 2, IsCompact (S j))
    (hGraph : ∀ (j : Fin 2) (t : ℝ), |t| < 2 * delta →
      ∀ x : E2, ‖x‖ < 2 →
        ((heightPlaneCoordinates u).symm (gRef x, c + t) ∈ S j ↔
          t = rho ^ 2 * ((J2 x).1 ^ 2 - (J2 x).2 ^ 2))) :
    let L := heightPlaneCoordinates u
    let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
    let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
    let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
    let xi : Fin 4 → ℝ → ℝ → E2 := fun k t r => J2.symm
      (sx k * Real.sqrt ((r ^ 2 + t / rho ^ 2) / 2),
        sy k * Real.sqrt ((r ^ 2 - t / rho ^ 2) / 2))
    let Xi : Fin 4 → ℝ → ℝ → E3 := fun k t r =>
      L.symm (gRef (xi k t r), c + t)
    let E : Fin 2 → ℝ → Set E2 := fun j t =>
      {x : E2 | L.symm (gRef x, c + t) ∈ S j ∧ 1 ≤ ‖x‖}
    let Ext : Fin 2 → ℝ → Set E3 := fun j t =>
      L.symm '' ((gRef '' E j t) ×ˢ ({c + t} : Set ℝ))
    let Mid : Fin 2 → ℝ → Set E3 := fun j t =>
      S j ∩ {y : E3 | H y = c + t}
    let MidBand : Fin 2 → Set E3 := fun j =>
      S j ∩ {y : E3 | |H y - c| ≤ delta}
    let OpenMidBand : Fin 2 → Set E3 := fun j =>
      S j ∩ {y : E3 | |H y - c| < delta}
    ∀ (hTrack : ∀ (j : Fin 2) (k : Fin 4) (r : ℝ),
        r ∈ Ioo (15 / 16 : ℝ) (17 / 16) →
        ∀ t : ℝ, |t| < 2 * delta →
          HasDerivAt (fun s : ℝ => Xi k s r) (X j (Xi k t r)) t)
      (T : Fin 2 → ℝ → ℝ →
        Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞)
      (hTself : ∀ (j : Fin 2) (s : ℝ) (y : E3), T j s s y = y)
      (hTtrack : ∀ (j : Fin 2) (s : ℝ), |s| < 2 * delta →
        ∀ y ∈ Ext j s, ∀ t : ℝ, |t| < 2 * delta →
          HasDerivAt (fun a : ℝ => T j s a y) (X j (T j s t y)) t)
      (hTimage : ∀ (j : Fin 2) (s t : ℝ),
        |s| ≤ 2 * delta → |t| ≤ 2 * delta →
          (T j s t) '' Ext j s = Ext j t ∧
          (T j s t).symm '' Ext j t = Ext j s)
      (J : ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
      (CJ : Set E2) (hCJ : IsCompact CJ)
      (hJ : ContDiff ℝ ∞ (fun p : ℝ × E2 => J p.1 p.2))
      (hJinv : ContDiff ℝ ∞ (fun p : ℝ × E2 => (J p.1).symm p.2))
      (hJzero : ∀ s : ℝ, s ≤ 0 → ∀ y : E2,
        J s y = y ∧ (J s).symm y = y)
      (hJone : ∀ s : ℝ, 1 ≤ s → ∀ y : E2,
        J s y = J 1 y ∧ (J s).symm y = (J 1).symm y)
      (hJsupport : ∀ s : ℝ,
        tsupport (fun y : E2 => J s y - y) ⊆ CJ ∧
        tsupport (fun y : E2 => (J s).symm y - y) ⊆ CJ)
      (hJdisc : gRef '' closedBall (0 : E2) 1 ⊆ CJᶜ)
      (hJimage :
        (J 1) '' (gRef '' E 0 0) = gRef '' E 1 0 ∧
        (J 1).symm '' (gRef '' E 1 0) = gRef '' E 0 0),
      ∃ (e : ℝ)
        (G : ℝ → Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞)
        (C3 : Set E3),
        0 < e ∧ e < 1 / 512 ∧ IsCompact C3 ∧
        ContDiff ℝ ∞ (fun p : ℝ × E3 => G p.1 p.2) ∧
        ContDiff ℝ ∞ (fun p : ℝ × E3 => (G p.1).symm p.2) ∧
        (∀ y : E3, G 0 y = y ∧ (G 0).symm y = y) ∧
        (∀ (s : ℝ) (y : E3),
          H (G s y) = H y ∧ H ((G s).symm y) = H y) ∧
        (∀ s : ℝ,
          tsupport (fun y : E3 => G s y - y) ⊆ C3 ∧
          tsupport (fun y : E3 => (G s).symm y - y) ⊆ C3) ∧
        (∀ (s : ℝ) (x : E2) (z : ℝ), ‖x‖ ≤ 1 + 2 * e →
          G s (L.symm (gRef x, z)) = L.symm (gRef x, z) ∧
          (G s).symm (L.symm (gRef x, z)) = L.symm (gRef x, z)) ∧
        (∀ (t : ℝ), |t| ≤ delta →
          G 1 '' Mid 0 t = Mid 1 t ∧
          (G 1).symm '' Mid 1 t = Mid 0 t) ∧
        G 1 '' MidBand 0 = MidBand 1 ∧
        (G 1).symm '' MidBand 1 = MidBand 0 ∧
        G 1 '' OpenMidBand 0 = OpenMidBand 1 ∧
        (G 1).symm '' OpenMidBand 1 = OpenMidBand 0 := by
  classical
  intro L H sx sy xi Xi E Ext Mid MidBand OpenMidBand
    hTrack T hTself hTtrack hTimage J CJ hCJ hJ hJinv hJzero hJone
    hJsupport hJdisc hJimage
  let U : Set E2 := gRef ⁻¹' CJᶜ
  have hU : IsOpen U := hCJ.isClosed.isOpen_compl.preimage gRef.continuous
  have hdiscU : closedBall (0 : E2) 1 ⊆ U := by
    intro x hx
    exact hJdisc ⟨x, hx, rfl⟩
  obtain ⟨eps, heps, hthick⟩ :=
    (isCompact_closedBall (0 : E2) 1).exists_thickening_subset_open hU hdiscU
  let e : ℝ := min (eps / 8) (1 / 1024)
  have he : 0 < e := lt_min (by positivity) (by norm_num)
  have heSmall : e < 1 / 512 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hepsBound : e ≤ eps / 8 := min_le_left _ _
  have hbuffer (x : E2) (hx : ‖x‖ ≤ 1 + 4 * e) : gRef x ∉ CJ := by
    apply hthick
    rw [thickening_closedBall heps (by norm_num : (0 : ℝ) ≤ 1)]
    simpa only [mem_ball, dist_zero_right] using
      (show ‖x‖ < eps + 1 by linarith only [hx, hepsBound, heps])
  let pi := horizontalBandProjection u
  let b : Fin 2 → ℝ × E2 → E2 := fun j p =>
    fderiv ℝ gRef.symm (gRef p.2)
      (pi (X j (L.symm (gRef p.2, c + p.1))))
  let P : Set E2 := gRef.symm '' (pi '' (S 0 ∪ S 1))
  have hNative := saddle_native_projected_fields
    u c rho delta e hrho hdelta hsmall he heSmall J2 hJ2 gRef X hX S hS hGraph hTrack
  obtain ⟨hb, hP, hExterior, hAnnulus⟩ := hNative
  obtain ⟨C, W, K, hC, hsC, hW, _hK, _hCs, _hWs, _hRad, _hCommon, hEq,
      KC, LC, KW, LW, hKC, hLC, hKW, hLW, hClock⟩ :=
    exists_saddle_common_middle_clock_data e delta he heSmall hdelta b hb P hP E
      hExterior (fun j t x ht hx hn => hAnnulus j t ht x hx hn)
  let Psi : ℝ → ℝ → D2 := clockEvolutionDiffeomorph C hKC hLC hC hsC
  let Phi : Fin 2 → ℝ → ℝ → D2 := fun j =>
    clockEvolutionDiffeomorph (W j) (hKW j) (hLW j) (hW j).1 (hW j).2
  let Kclock : Set E2 :=
    (Prod.snd '' tsupport C) ∪ ⋃ j : Fin 2, Prod.snd '' tsupport (W j)
  obtain ⟨hKclock, _hPsiFormula, hPhiFormula, _hPsiSmooth, hPhiSmooth, hPsiNorm,
    hAgree, _hPsiSupp, _hPhiSupp, hFixed, _hImages, _hDeriv, _hTracks⟩ := hClock
  have hClockExterior := saddle_common_middle_exterior_images u c delta hdelta
    gRef X S T hTself hTtrack hTimage W hW KW LW hKW hLW hEq
  let A : Fin 2 → ℝ → D2 := fun j t => (gRef.symm.trans (Phi j 0 t)).trans gRef
  have hAf (j : Fin 2) (t : ℝ) (x : E2) :
      A j t x = gRef (Phi j 0 t (gRef.symm x)) := rfl
  have hAi (j : Fin 2) (t : ℝ) (x : E2) :
      (A j t).symm x = gRef ((Phi j 0 t).symm (gRef.symm x)) := rfl
  have hASmooth (j : Fin 2) :
      ContDiff ℝ ∞ (fun p : ℝ × E2 => A j p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × E2 => (A j p.1).symm p.2) :=
    ⟨gRef.contDiff.comp ((hPhiSmooth j).1.comp
      ((contDiff_const.prodMk contDiff_fst).prodMk
        (gRef.symm.contDiff.comp contDiff_snd))),
     gRef.contDiff.comp ((hPhiSmooth j).2.comp
      ((contDiff_const.prodMk contDiff_fst).prodMk
        (gRef.symm.contDiff.comp contDiff_snd)))⟩
  clear_value A
  have hAzero (j : Fin 2) (x : E2) : A j 0 x = x ∧ (A j 0).symm x = x := by
    have hf : A j 0 x = x := by
      rw [hAf, (hPhiFormula j 0 0 _).1, clockEvolution_self,
        gRef.apply_symm_apply]
    exact ⟨hf, equiv_symm_fixed_of_fixed (A j 0).toEquiv hf⟩
  have hAimage (j : Fin 2) (t : ℝ) (ht : |t| ≤ delta) :
      A j t '' (gRef '' E j 0) = gRef '' E j t ∧
      (A j t).symm '' (gRef '' E j t) = gRef '' E j 0 := by
    constructor
    · calc
        _ = gRef '' (Phi j 0 t '' E j 0) := by
          simp only [image_image, hAf, gRef.symm_apply_apply]
        _ = _ := congrArg (Set.image gRef) (hClockExterior j t ht).1
    · calc
        _ = gRef '' ((Phi j 0 t).symm '' E j t) := by
          simp only [image_image, hAi, gRef.symm_apply_apply]
        _ = _ := congrArg (Set.image gRef) (hClockExterior j t ht).2
  have hJfix (s : ℝ) (x : E2) (hx : x ∉ CJ) : J s x = x := by
    have hnot : x ∉ tsupport (fun y : E2 => J s y - y) :=
      fun hh => hx ((hJsupport s).1 hh)
    have hz : (fun y : E2 => J s y - y) x = 0 :=
      image_eq_zero_of_notMem_tsupport (f := fun y : E2 => J s y - y) hnot
    exact sub_eq_zero.mp hz
  obtain ⟨zeta, hzeta, hczeta, _hszeta, hnearZeta, _hzetaBounds⟩ :=
    exists_compact_smooth_cutoff (K := Icc (-delta) delta)
      (U := Ioo (-3 * delta / 2) (3 * delta / 2))
      isCompact_Icc isOpen_Ioo (fun _ hx =>
        ⟨by linarith only [hx.1, hdelta], by linarith only [hx.2, hdelta]⟩)
  have hzetaOne (t : ℝ) (ht : |t| ≤ delta) : zeta t = 1 :=
    (eventually_nhdsSet_iff_forall.mp hnearZeta t (abs_le.mp ht)).self_of_nhds
  let v : ℝ → ℝ → ℝ := fun s t => s * zeta t
  let a : ℝ → ℝ → ℝ := fun s t => v s t * t
  let M : ℝ → ℝ → D2 := fun s t =>
    ((A 0 (a s t)).symm.trans (J (v s t))).trans (A 1 (a s t))
  have hMf (s t : ℝ) (x : E2) :
      M s t x = A 1 (a s t) (J (v s t) ((A 0 (a s t)).symm x)) := rfl
  have hMi (s t : ℝ) (x : E2) :
      (M s t).symm x = A 0 (a s t) ((J (v s t)).symm ((A 1 (a s t)).symm x)) :=
    rfl
  have hv : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × E2 => v p.1.1 p.1.2) :=
    contDiff_fst.fst.mul (hzeta.comp contDiff_fst.snd)
  have ha : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × E2 => a p.1.1 p.1.2) :=
    hv.mul contDiff_fst.snd
  have hM : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × E2 => M p.1.1 p.1.2 p.2) :=
    (hASmooth 1).1.comp (ha.prodMk
      (hJ.comp (hv.prodMk ((hASmooth 0).2.comp (ha.prodMk contDiff_snd)))))
  have hMinv : ContDiff ℝ ∞
      (fun p : (ℝ × ℝ) × E2 => (M p.1.1 p.1.2).symm p.2) :=
    (hASmooth 0).1.comp (ha.prodMk
      (hJinv.comp (hv.prodMk ((hASmooth 1).2.comp (ha.prodMk contDiff_snd)))))
  clear_value M
  have hMzero (t : ℝ) (x : E2) : M 0 t x = x := by
    rw [hMf]
    simp only [a, v, zero_mul, (hAzero 0 x).2, (hJzero 0 le_rfl x).1,
      (hAzero 1 x).1]
  have hMzeta (s t : ℝ) (hz : zeta t = 0) (x : E2) : M s t x = x := by
    rw [hMf]
    simp only [a, v, hz, mul_zero, zero_mul, (hAzero 0 x).2,
      (hJzero 0 le_rfl x).1, (hAzero 1 x).1]
  have hMdisc (s t : ℝ) (x : E2) (hx : ‖x‖ ≤ 1 + 2 * e) :
      M s t (gRef x) = gRef x ∧ (M s t).symm (gRef x) = gRef x := by
    have hi : (A 0 (a s t)).symm (gRef x) =
        gRef ((Psi 0 (a s t)).symm x) := by
      rw [hAi, gRef.symm_apply_apply, (hAgree 0 0 (a s t) x hx).2]
    have hn : ‖(Psi 0 (a s t)).symm x‖ ≤ 1 + 2 * e := by
      rw [(hPsiNorm 0 (a s t) x).2]
      exact hx
    have hj : J (v s t) (gRef ((Psi 0 (a s t)).symm x)) =
        gRef ((Psi 0 (a s t)).symm x) :=
      hJfix _ _ (hbuffer _ (by linarith only [hn, he]))
    have hf : M s t (gRef x) = gRef x := by
      rw [hMf, hi, hj, hAf, gRef.symm_apply_apply,
        (hAgree 1 0 (a s t) _ hn).1, (Psi 0 (a s t)).apply_symm_apply]
    exact ⟨hf, equiv_symm_fixed_of_fixed (M s t).toEquiv hf⟩
  let Cphys : Set E2 := (gRef '' Kclock) ∪ CJ
  have hCphys : IsCompact Cphys := (hKclock.image gRef.continuous).union hCJ
  have hMfix (s t : ℝ) (x : E2) (hx : x ∉ Cphys) : M s t x = x := by
    have hn : gRef.symm x ∉ Kclock := by
      intro hh
      exact hx (Or.inl ⟨gRef.symm x, hh, gRef.apply_symm_apply x⟩)
    have hAfixed (j : Fin 2) : A j (a s t) x = x ∧ (A j (a s t)).symm x = x := by
      constructor
      · rw [hAf, ((hFixed 0 (a s t) (gRef.symm x) hn).2 j).1,
          gRef.apply_symm_apply]
      · rw [hAi, ((hFixed 0 (a s t) (gRef.symm x) hn).2 j).2,
          gRef.apply_symm_apply]
    rw [hMf, (hAfixed 0).2, hJfix _ _ (fun hh => hx (Or.inr hh)),
      (hAfixed 1).1]
  have hMimage (t : ℝ) (ht : |t| ≤ delta) :
      M 1 t '' (gRef '' E 0 t) = gRef '' E 1 t ∧
      (M 1 t).symm '' (gRef '' E 1 t) = gRef '' E 0 t := by
    have hv1 : v 1 t = 1 := by simp only [v, hzetaOne t ht, one_mul]
    have ha1 : a 1 t = t := by simp only [a, hv1, one_mul]
    have hj : (J (v 1 t) : E2 → E2) = J 1 := by
      funext x
      exact (hJone (v 1 t) (by rw [hv1]) x).1
    have hji : ((J (v 1 t)).symm : E2 → E2) = (J 1).symm := by
      funext x
      exact (hJone (v 1 t) (by rw [hv1]) x).2
    constructor
    · calc
        _ = A 1 t '' (J 1 '' ((A 0 t).symm '' (gRef '' E 0 t))) := by
          simp only [image_image, hMf, ha1, hj]
        _ = _ := by rw [(hAimage 0 t ht).2, hJimage.1, (hAimage 1 t ht).1]
    · calc
        _ = A 0 t '' ((J 1).symm '' ((A 1 t).symm '' (gRef '' E 1 t))) := by
          simp only [image_image, hMi, ha1, hji]
        _ = _ := by rw [(hAimage 1 t ht).2, hJimage.2, (hAimage 0 t ht).1]
  have hMshift (s : ℝ) :
      ContDiff ℝ ∞ (fun p : ℝ × E2 => M s (p.1 - c) p.2) :=
    hM.comp ((contDiff_const.prodMk (contDiff_fst.sub contDiff_const)).prodMk contDiff_snd)
  have hMshiftInv (s : ℝ) :
      ContDiff ℝ ∞ (fun p : ℝ × E2 => (M s (p.1 - c)).symm p.2) :=
    hMinv.comp
      ((contDiff_const.prodMk (contDiff_fst.sub contDiff_const)).prodMk contDiff_snd)
  let Q (s : ℝ) := planarFamilyGraphDiffeomorph (fun z => M s (z - c))
    (hMshift s) (hMshiftInv s)
  let G : ℝ → D3 := fun s => (L.toDiffeomorph.trans (Q s)).trans L.symm.toDiffeomorph
  have hformula (s : ℝ) (x : E2) (z : ℝ) :
      G s (L.symm (x, z)) = L.symm (M s (z - c) x, z) ∧
      (G s).symm (L.symm (x, z)) = L.symm ((M s (z - c)).symm x, z) := by
    constructor
    · change L.symm (Q s (L (L.symm (x, z)))) = _
      rw [L.apply_symm_apply]
      rfl
    · change L.symm ((Q s).symm (L (L.symm (x, z)))) = _
      rw [L.apply_symm_apply]
      rfl
  have hGsmooth : ContDiff ℝ ∞ (fun p : ℝ × E3 => G p.1 p.2) :=
    L.symm.contDiff.comp ((hM.comp
      ((contDiff_fst.prodMk ((L.contDiff.comp contDiff_snd).snd.sub contDiff_const)).prodMk
        (L.contDiff.comp contDiff_snd).fst)).prodMk (L.contDiff.comp contDiff_snd).snd)
  have hGismooth : ContDiff ℝ ∞ (fun p : ℝ × E3 => (G p.1).symm p.2) :=
    L.symm.contDiff.comp ((hMinv.comp
      ((contDiff_fst.prodMk ((L.contDiff.comp contDiff_snd).snd.sub contDiff_const)).prodMk
        (L.contDiff.comp contDiff_snd).fst)).prodMk (L.contDiff.comp contDiff_snd).snd)
  clear_value G
  have hGzero (y : E3) : G 0 y = y ∧ (G 0).symm y = y := by
    have hf := (hformula 0 (L y).1 (L y).2).1
    rw [hMzero, L.symm_apply_apply] at hf
    exact ⟨hf, equiv_symm_fixed_of_fixed (G 0).toEquiv hf⟩
  have hLH (y : E3) : (L y).2 = H y := heightPlaneCoordinates_snd u y
  have hHeight (s : ℝ) (y : E3) :
      H (G s y) = H y ∧ H ((G s).symm y) = H y := by
    have hf := (hformula s (L y).1 (L y).2).1
    have hi := (hformula s (L y).1 (L y).2).2
    rw [L.symm_apply_apply] at hf hi
    constructor
    · rw [← hLH, hf, L.apply_symm_apply, hLH]
    · rw [← hLH, hi, L.apply_symm_apply, hLH]
  have hGdisc (s : ℝ) (x : E2) (z : ℝ) (hx : ‖x‖ ≤ 1 + 2 * e) :
      G s (L.symm (gRef x, z)) = L.symm (gRef x, z) ∧
      (G s).symm (L.symm (gRef x, z)) = L.symm (gRef x, z) := by
    obtain ⟨hf, hi⟩ := hformula s (gRef x) z
    rw [(hMdisc s (z - c) x hx).1] at hf
    rw [(hMdisc s (z - c) x hx).2] at hi
    exact ⟨hf, hi⟩
  let C3 : Set E3 := L.symm '' (Cphys ×ˢ ((fun t : ℝ => c + t) '' tsupport zeta))
  have hC3 : IsCompact C3 :=
    (hCphys.prod (hczeta.isCompact.image (continuous_const.add continuous_id))).image
      L.symm.continuous
  have hGfix (s : ℝ) (y : E3) (hy : y ∉ C3) : G s y = y := by
    let x : E2 := (L y).1
    let z : ℝ := (L y).2
    have hc : L.symm (x, z) = y := L.symm_apply_apply y
    have hf := (hformula s x z).1
    by_cases hx : x ∈ Cphys
    · have hz : z - c ∉ tsupport zeta := by
        intro hh
        apply hy
        exact ⟨(x, z), ⟨hx, ⟨z - c, hh, by ring⟩⟩, hc⟩
      rw [hMzeta s (z - c) (image_eq_zero_of_notMem_tsupport hz), hc] at hf
      exact hf
    · rw [hMfix s (z - c) x hx, hc] at hf
      exact hf
  have hGsupport (s : ℝ) :
      tsupport (fun y : E3 => G s y - y) ⊆ C3 ∧
      tsupport (fun y : E3 => (G s).symm y - y) ⊆ C3 := by
    constructor
    · apply closure_minimal ?_ hC3.isClosed
      intro y hy
      by_contra hn
      exact hy (sub_eq_zero.mpr (hGfix s y hn))
    · apply closure_minimal ?_ hC3.isClosed
      intro y hy
      by_contra hn
      exact hy (sub_eq_zero.mpr
        (equiv_symm_fixed_of_fixed (G s).toEquiv (hGfix s y hn)))
  have hLevelMaps (t : ℝ) (ht : |t| ≤ delta) :
      MapsTo (G 1) (Mid 0 t) (Mid 1 t) ∧
      MapsTo (G 1).symm (Mid 1 t) (Mid 0 t) := by
    have hmap (j k : Fin 2) (F : D3) (MF : D2)
        (hf : ∀ x : E2, F (L.symm (x, c + t)) = L.symm (MF x, c + t))
        (hh : ∀ y : E3, H (F y) = H y)
        (hfix : ∀ x : E2, ‖x‖ ≤ 1 + 2 * e →
          F (L.symm (gRef x, c + t)) = L.symm (gRef x, c + t))
        (himage : MF '' (gRef '' E j t) = gRef '' E k t) :
        MapsTo F (Mid j t) (Mid k t) := by
      intro y hy
      let x : E2 := gRef.symm (L y).1
      have hc : L.symm (gRef x, c + t) = y := by
        have hz : (L y).2 = c + t := (hLH y).trans hy.2
        calc
          _ = L.symm ((L y).1, (L y).2) := by rw [gRef.apply_symm_apply, hz]
          _ = y := L.symm_apply_apply y
      refine ⟨?_, (hh y).trans hy.2⟩
      by_cases hx : ‖x‖ < 1
      · have hfixed := hfix x (by linarith only [hx, he])
        rw [hc] at hfixed
        rw [hfixed, ← hc]
        exact (hGraph k t (by linarith only [ht, hdelta]) x (by linarith only [hx])).mpr
          ((hGraph j t (by linarith only [ht, hdelta]) x (by linarith only [hx])).mp
            (hc.symm ▸ hy.1))
      · have hxE : x ∈ E j t := ⟨hc.symm ▸ hy.1, le_of_not_gt hx⟩
        have hout : MF (gRef x) ∈ gRef '' E k t := by
          rw [← himage]
          exact ⟨gRef x, ⟨x, hxE, rfl⟩, rfl⟩
        obtain ⟨x', hx', hxx'⟩ := hout
        have hFy := hf (gRef x)
        rw [hc, ← hxx'] at hFy
        rw [hFy]
        exact hx'.1
    constructor
    · exact hmap 0 1 (G 1) (M 1 t)
        (fun x => by simpa only [add_sub_cancel_left] using (hformula 1 x (c + t)).1)
        (fun y => (hHeight 1 y).1) (fun x hx => (hGdisc 1 x (c + t) hx).1)
        (hMimage t ht).1
    · exact hmap 1 0 (G 1).symm (M 1 t).symm
        (fun x => by simpa only [add_sub_cancel_left] using (hformula 1 x (c + t)).2)
        (fun y => (hHeight 1 y).2) (fun x hx => (hGdisc 1 x (c + t) hx).2)
        (hMimage t ht).2
  have himages (F : D3) (V Z : Set E3)
      (hf : MapsTo F V Z) (hi : MapsTo F.symm Z V) :
      F '' V = Z ∧ F.symm '' Z = V := by
    constructor
    · apply Subset.antisymm
      · rintro _ ⟨x, hx, rfl⟩
        exact hf hx
      · intro y hy
        exact ⟨F.symm y, hi hy, F.apply_symm_apply y⟩
    · apply Subset.antisymm
      · rintro _ ⟨x, hx, rfl⟩
        exact hi hx
      · intro y hy
        exact ⟨F y, hf hy, F.symm_apply_apply y⟩
  have hLevelImages (t : ℝ) (ht : |t| ≤ delta) :
      G 1 '' Mid 0 t = Mid 1 t ∧ (G 1).symm '' Mid 1 t = Mid 0 t :=
    himages (G 1) (Mid 0 t) (Mid 1 t) (hLevelMaps t ht).1 (hLevelMaps t ht).2
  have hBandMaps (j k : Fin 2) (F : D3)
      (hh : ∀ y : E3, H (F y) = H y)
      (hm : ∀ t : ℝ, |t| ≤ delta → MapsTo F (Mid j t) (Mid k t)) :
      MapsTo F (MidBand j) (MidBand k) ∧
      MapsTo F (OpenMidBand j) (OpenMidBand k) := by
    constructor
    · intro y hy
      have ht : y ∈ Mid j (H y - c) := ⟨hy.1, by dsimp; ring⟩
      exact ⟨(hm (H y - c) hy.2 ht).1,
        by simpa only [mem_ofPred_eq, hh y] using hy.2⟩
    · intro y hy
      have ht : y ∈ Mid j (H y - c) := ⟨hy.1, by dsimp; ring⟩
      exact ⟨(hm (H y - c) hy.2.le ht).1,
        by simpa only [mem_ofPred_eq, hh y] using hy.2⟩
  have hforward := hBandMaps 0 1 (G 1) (fun y => (hHeight 1 y).1)
    (fun t ht => (hLevelMaps t ht).1)
  have hinverse := hBandMaps 1 0 (G 1).symm (fun y => (hHeight 1 y).2)
    (fun t ht => (hLevelMaps t ht).2)
  exact ⟨e, G, C3, he, heSmall, hC3, hGsmooth, hGismooth, hGzero, hHeight,
    hGsupport, hGdisc, hLevelImages,
    (himages (G 1) (MidBand 0) (MidBand 1) hforward.1 hinverse.1).1,
    (himages (G 1) (MidBand 0) (MidBand 1) hforward.1 hinverse.1).2,
    (himages (G 1) (OpenMidBand 0) (OpenMidBand 1) hforward.2 hinverse.2).1,
    (himages (G 1) (OpenMidBand 0) (OpenMidBand 1) hforward.2 hinverse.2).2⟩

end PoincareConjecture.M25.Topology3D
