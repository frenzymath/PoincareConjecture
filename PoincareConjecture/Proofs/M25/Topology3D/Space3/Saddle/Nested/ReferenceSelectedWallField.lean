import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.Nested.ReferenceHighRegularity
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NestedReferenceBufferedChart
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NestedReferenceCollar
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.SelectedWallField

set_option autoImplicit false

open Set Metric Filter Function
open scoped ContDiff Manifold InnerProductSpace Topology Matrix NNReal

namespace PoincareConjecture.M25.Topology3D.NestedReferenceLower




theorem exists_reference_selected_wall_field
    (ws wm d sigma : ℝ)
    (hwslo : (1 : ℝ) / 2 < ws) (hwshi : ws < 3 / 4)
    (hwsroot : (2 - 1 / ws) * Real.sqrt (1 - ws ^ 2) = 1 / 32)
    (hwmlo : 0 < wm) (hwmhi : wm < 1 / 2)
    (hwmroot : (2 - 1 / wm) * Real.sqrt (1 - wm ^ 2) = -(1 / 32))
    (hsigma : sigma = 1 ∨ sigma = -1)
    (m : OpenPartialHomeomorph E2 (ℝ × ℝ))
    (hm_point : (!₂[-Real.sqrt (1 - ws ^ 2), 0] : E2) ∈ m.source)
    (hm_source : m.source ⊆ Metric.ball (0 : E2) 1)
    (hm_zero : m (!₂[-Real.sqrt (1 - ws ^ 2), 0] : E2) = 0)
    (hm : ContDiffOn ℝ ∞ m m.source)
    (hmi : ContDiffOn ℝ ∞ m.symm m.target)
    (hm_height : ∀ v ∈ m.source,
      ‖v‖ ^ 2 + Real.sqrt (1 - ‖v‖ ^ 2) + v 0 / 32 =
        1 - ws ^ 2 + ws - Real.sqrt (1 - ws ^ 2) / 32 -
          (m v).1 ^ 2 + (m v).2 ^ 2) :
    let h8 := exists_nestedReference_buffered_morse_chart
      ws hwslo hwshi m hm_point hm_source hm_zero hm hmi hm_height
    let R : ℝ := Classical.choose h8
    let h8R := Classical.choose_spec h8
    let _b : ℝ := Classical.choose h8R
    let h8b := Classical.choose_spec h8R
    let e : OpenPartialHomeomorph UnitTwoSphere (ℝ × ℝ) :=
      Classical.choose h8b
    let rhoN : ℝ := R / 2
    let k : ℝ := 1 - ws ^ 2 + ws - Real.sqrt (1 - ws ^ 2) / 32
    let mu : ℝ := 1 - wm ^ 2 + wm + Real.sqrt (1 - wm ^ 2) / 32
    ∀ delta : ℝ, 0 < delta → delta ≤ rhoN ^ 2 / 128 →
      4 * delta < k - 17 / 16 → 4 * delta < mu - k →
    let psi : UnitTwoSphere × ℝ → E3 := fun p =>
      nestedReferenceDiffeomorph d ((1 + p.2) • (p.1 : E3))
    let j : UnitTwoSphere → E3 := fun q => psi (q, 0)
    let H0 : E3 → ℝ := fun y => (heightCoordinates y).2
    let U : Set E3 := psi '' (univ ×ˢ Ioo (-1) 1)
    let r2 : ℝ × ℝ → ℝ := fun s => s.1 ^ 2 + s.2 ^ 2
    let Do : ℝ → Set UnitTwoSphere := fun r =>
      e.symm '' {s | r2 s < r ^ 2}
    let Dc : ℝ → Set UnitTwoSphere := fun r =>
      e.symm '' {s | r2 s ≤ r ^ 2}
    let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
    let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
    let xi : Fin 4 → (ℝ × ℝ) → (ℝ × ℝ) := fun i p =>
      (sx i * Real.sqrt ((rhoN ^ 2 * (1 + p.2) ^ 2 + p.1) / 2),
        sy i * Real.sqrt ((rhoN ^ 2 * (1 + p.2) ^ 2 - p.1) / 2))
    let q : Fin 4 → (ℝ × ℝ) → UnitTwoSphere := fun i p =>
      e.symm (sigma * (xi i p).2, sigma * (xi i p).1)
    ∃ (f : E3 → ℝ) (X : E3 → E3),
      ContDiffOn ℝ ∞ f U ∧
      (∀ p ∈ (univ ×ˢ Ioo (-1) 1 : Set (UnitTwoSphere × ℝ)),
        f (psi p) = p.2) ∧
      ContDiff ℝ ∞ X ∧ HasCompactSupport X ∧
      tsupport X ⊆ (U ∩ {y : E3 | |H0 y - (k + d)| < 4 * delta}) \
        (j '' Dc (rhoN / 4)) ∧
      (∀ y : E3, fderiv ℝ f y (X y) = 0) ∧
      (∀ p : UnitTwoSphere, |H0 (j p) - (k + d)| ≤ 3 * delta →
        p ∉ Do (rhoN / 2) → H0 (X (j p)) = 1) ∧
      (∀ r : ℝ, 0 < r → r ≤ 5 * rhoN / 4 →
        IsOpen (Do r) ∧ IsCompact (Dc r) ∧ closure (Do r) = Dc r) ∧
      (∀ i : Fin 4, ∀ a : ℝ, |a| < 1 / 8 →
        ∀ t : ℝ, |t| ≤ 2 * delta →
          q i (t, a) ∈ e.source ∧
          H0 (j (q i (t, a))) = k + d + t ∧
          r2 (e (q i (t, a))) = rhoN ^ 2 * (1 + a) ^ 2) ∧
      (∀ t : ℝ, |t| ≤ 2 * delta →
        {p : UnitTwoSphere | p ∈ Dc rhoN \ Do rhoN ∧
          H0 (j p) = k + d + t} =
            range (fun i : Fin 4 => q i (t, 0))) ∧
      ∀ i : Fin 4, ∀ a : ℝ, |a| < 1 / 8 →
        ∀ t : ℝ, |t| ≤ 2 * delta →
          HasDerivAt (fun v : ℝ => j (q i (v, a)))
            (X (j (q i (t, a)))) t := by
  classical
  intro h8 R h8R b h8b e rhoN k mu delta hdelta hd hgapLo hgapHi
    psi j H0 U r2 Do Dc sx sy xi q
  obtain ⟨P, hR, _hb, _hbSmall, _hRbudget, _hbHeight, hpCoordinates,
    _hesource, _hetarget, _heform, _heinv, hpsource, hepstar, hesmooth,
    heismooth, heheight, _hcritical, _hPsource, _hPtarget, hbuffer,
    _hPform, _hPinv, _hPsubset, _hPzero, _hPsm, _hPism, _hProduct⟩ :=
      Classical.choose_spec h8b
  let pstar : UnitTwoSphere := northSpherePoint
    ((1 + ws)⁻¹ • (!₂[-Real.sqrt (1 - ws ^ 2), 0] : E2))
  change 0 < R at hR
  change heightCoordinates (pstar : E3) =
    ((!₂[-Real.sqrt (1 - ws ^ 2), 0] : E2), ws) at hpCoordinates
  change pstar ∈ e.source at hpsource
  change e pstar = 0 at hepstar
  change ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ e e.source at hesmooth
  change ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ e.symm e.target at heismooth
  change (∀ d : ℝ, ∀ p ∈ e.source,
    (heightCoordinates (nestedReferenceDiffeomorph d (p : E3))).2 =
      k + d - (e p).1 ^ 2 + (e p).2 ^ 2) at heheight
  change {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 ≤ (2 * R) ^ 2} ⊆ e.target at hbuffer
  clear_value R e
  clear _hb _hbSmall _hRbudget _hbHeight _hesource _hetarget _heform _heinv
    _hcritical _hPsource _hPtarget _hPform _hPinv _hPsubset _hPzero
    _hPsm _hPism _hProduct P h8b b h8R h8
  let rho : ℝ := rhoN
  let c : ℝ := k + d
  let H : E3 →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ E2 ℝ).comp heightCoordinates.toContinuousLinearMap
  let u : E3 := heightCoordinates.symm ((0 : E2), (1 : ℝ))
  have hu (y : E3) : ⟪u, y⟫_ℝ = H y := by
    simp [u, H, heightCoordinates_symm_apply, EuclideanSpace.inner_eq_star_dotProduct,
      dotProduct, Fin.sum_univ_three]
  have hpsi := (exists_nestedReference_collar d).1
  change IsCollarEmbedding psi at hpsi
  have hLevel (p : UnitTwoSphere) : H (j p) =
      (heightCoordinates (nestedReferenceDiffeomorph d (p : E3))).2 := by
    simp only [j, psi, add_zero, one_smul]
    rfl
  have hNative : (fun p : UnitTwoSphere => ⟪u, psi (p, 0)⟫_ℝ) =
      (fun p : UnitTwoSphere =>
        (heightCoordinates (nestedReferenceDiffeomorph d (p : E3))).2) := by
    funext p
    rw [hu]
    exact hLevel p
  obtain ⟨_hSmooth, _hklo, _hkhi, _hmulo, hqs, _hqm, _hks, hmum,
    hclass, _hNoncritical, _hRegular⟩ :=
    reference_high_sphere_regularity ws wm d hwslo hwshi hwsroot hwmlo hwmhi hwmroot
  have hqsEq : -southSpherePoint (-(!₂[-Real.sqrt (1 - ws ^ 2), 0] : E2)) =
      pstar := Subtype.ext (heightCoordinates.injective (hqs.trans hpCoordinates.symm))
  let vm : E2 := !₂[Real.sqrt (1 - wm ^ 2), 0]
  have hwmrad : 0 ≤ 1 - wm ^ 2 := by nlinarith only [hwmlo, hwmhi]
  have hNorm (v : E2) : ‖v‖ ^ 2 = (v 0) ^ 2 + (v 1) ^ 2 := by
    simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  have hvmNorm : ‖vm‖ ^ 2 = 1 - wm ^ 2 := by
    rw [hNorm]
    change Real.sqrt (1 - wm ^ 2) ^ 2 + (0 : ℝ) ^ 2 = _
    nlinarith only [Real.sq_sqrt hwmrad]
  have hmuVal : ‖vm‖ ^ 2 + Real.sqrt (1 - ‖vm‖ ^ 2) + vm 0 / 32 = mu := by
    rw [hvmNorm, sub_sub_cancel, Real.sqrt_sq_eq_abs, abs_of_pos hwmlo]
    rfl
  have hsigmaSq : sigma ^ 2 = 1 := by
    rcases hsigma with h | h <;> simp only [h] <;> norm_num
  let N : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) := {
    toFun := fun s => (sigma * s.2, sigma * s.1)
    invFun := fun s => (sigma * s.2, sigma * s.1)
    map_add' := by intro s t; ext <;> simp [mul_add]
    map_smul' := by intro a s; ext <;> simp [smul_eq_mul] <;> ring
    left_inv := by
      intro s
      apply Prod.ext <;> dsimp <;> rw [← mul_assoc, ← pow_two, hsigmaSq, one_mul]
    right_inv := by
      intro s
      apply Prod.ext <;> dsimp <;> rw [← mul_assoc, ← pow_two, hsigmaSq, one_mul]
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  have hN (s : ℝ × ℝ) :
      N (N s) = s ∧
      (N s).1 ^ 2 + (N s).2 ^ 2 = s.1 ^ 2 + s.2 ^ 2 ∧
      -(N s).1 ^ 2 + (N s).2 ^ 2 = s.1 ^ 2 - s.2 ^ 2 := by
    refine ⟨N.left_inv s, ?_, ?_⟩
    · change (sigma * s.2) ^ 2 + (sigma * s.1) ^ 2 = _
      rw [mul_pow, mul_pow, hsigmaSq, one_mul, one_mul]
      ring
    · change -(sigma * s.2) ^ 2 + (sigma * s.1) ^ 2 = _
      rw [mul_pow, mul_pow, hsigmaSq, one_mul, one_mul]
      ring
  have hmorse : {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 < (2 * R) ^ 2} ⊆ e.target :=
    fun s hs => hbuffer (show s.1 ^ 2 + s.2 ^ 2 ≤ (2 * R) ^ 2 from hs.le)
  have hrho : 0 < rho := half_pos hR
  have hrho2 : 0 < rho ^ 2 := sq_pos_of_pos hrho
  have hj := (collar_central_contMDiff psi hpsi).continuous
  have hji : Injective j := by
    intro p z hpz
    exact congrArg Prod.fst (hpsi.2.1
      ⟨mem_univ _, by norm_num⟩ ⟨mem_univ _, by norm_num⟩ hpz)
  have hU : IsOpen U := collar_image_open psi hpsi
  have hjU (p : UnitTwoSphere) : j p ∈ U :=
    ⟨(p, 0), ⟨mem_univ _, by norm_num⟩, rfl⟩
  have hrs : ContDiff ℝ ∞ r2 := by dsimp [r2]; fun_prop
  have hBtarget (r : ℝ) (hr : 0 < r) (hrr : r ≤ 5 * rho / 4) :
      {s : ℝ × ℝ | r2 s ≤ r ^ 2} ⊆ e.target := by
    intro s hs
    change r2 s ≤ r ^ 2 at hs
    apply hmorse
    have hsq := (sq_le_sq₀ hr.le (by positivity : 0 ≤ 5 * rho / 4)).mpr hrr
    change r2 s < (2 * R) ^ 2
    dsimp only [rho, rhoN] at hsq
    nlinarith only [hs, hsq, sq_pos_of_pos hR]
  have hgeom (r : ℝ) (hr : 0 < r) (hrr : r ≤ 5 * rho / 4) :
      IsOpen (Do r) ∧ IsCompact (Dc r) ∧ closure (Do r) = Dc r := by
    obtain ⟨ho, hc, hcl⟩ := morseRadialDisc_geometry r hr
    have hsub : {s | r2 s < r ^ 2} ⊆ {s | r2 s ≤ r ^ 2} :=
      fun s hs => (show r2 s < r ^ 2 from hs).le
    have hct : IsCompact (Dc r) := hc.image_of_continuousOn
      (e.symm.continuousOn.mono (hBtarget r hr hrr))
    refine ⟨e.symm.isOpen_image_of_subset_source ho
      (hsub.trans (hBtarget r hr hrr)), hct, Subset.antisymm ?_ ?_⟩
    · exact closure_minimal (image_mono hsub) hct.isClosed
    · rintro p ⟨s, hs, rfl⟩
      exact mem_closure_image
        (e.symm.continuousOn.continuousAt
          (e.open_target.mem_nhds (hBtarget r hr hrr hs))) (hcl.symm ▸ hs)
  have hDoMem (r : ℝ) (hr : 0 < r) (hrr : r ≤ 5 * rho / 4) (p : UnitTwoSphere) :
      p ∈ Do r ↔ p ∈ e.source ∧ r2 (e p) < r ^ 2 := by
    constructor
    · rintro ⟨s, hs, rfl⟩
      change r2 s < r ^ 2 at hs
      have ht := hBtarget r hr hrr hs.le
      exact ⟨e.map_target ht, by simpa only [e.right_inv ht] using hs⟩
    · rintro ⟨hp, hs⟩
      exact ⟨e p, hs, e.left_inv hp⟩
  have hDcMem (r : ℝ) (hr : 0 < r) (hrr : r ≤ 5 * rho / 4) (p : UnitTwoSphere) :
      p ∈ Dc r ↔ p ∈ e.source ∧ r2 (e p) ≤ r ^ 2 := by
    constructor
    · rintro ⟨s, hs, rfl⟩
      change r2 s ≤ r ^ 2 at hs
      have ht := hBtarget r hr hrr hs
      exact ⟨e.map_target ht, by simpa only [e.right_inv ht] using hs⟩
    · rintro ⟨hp, hs⟩
      exact ⟨e p, hs, e.left_inv hp⟩
  have hpoint : pstar ∈ e.source := hpsource
  have hpointDo : pstar ∈ Do (rho / 2) := by
    apply (hDoMem _ (by positivity) (by linarith only [hrho]) _).mpr
    refine ⟨hpoint, ?_⟩
    rw [hepstar]
    simpa only [r2, Prod.fst_zero, Prod.snd_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
      add_zero] using sq_pos_of_pos (show 0 < rho / 2 by positivity)
  let Ksrc : Set UnitTwoSphere := {p | |H (j p) - c| ≤ 3 * delta} \ Do (rho / 2)
  have hKsrc : IsCompact Ksrc :=
    ((isClosed_le ((H.continuous.comp hj).sub continuous_const).abs continuous_const).inter
      (hgeom _ (by positivity) (by linarith only [hrho])).1.isClosed_compl).isCompact
  have hreg (p : UnitTwoSphere) (hp : p ∈ Ksrc) :
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
        (fun z : UnitTwoSphere => ⟪u, psi (z, 0)⟫_ℝ) p ≠ 0 := by
    intro hz
    have hheight : |H (j p) - c| ≤ 3 * delta := hp.1
    have hh := abs_le.mp hheight
    have hpHigh : (17 : ℝ) / 16 <
        (heightCoordinates (nestedReferenceDiffeomorph d (p : E3))).2 - d := by
      rw [← hLevel]
      change -(3 * delta) ≤ H (j p) - (k + d) ∧
        H (j p) - (k + d) ≤ 3 * delta at hh
      linarith only [hh.1, hgapLo, hdelta]
    rw [hNative] at hz
    rcases ((hclass p hpHigh).2.2.2).mp hz with heq | heq
    · exact hp.2 ((heq.trans hqsEq).symm ▸ hpointDo)
    · have hpMax : H (j p) = mu + d := by
        rw [hLevel, heq]
        exact hmum.trans (congrArg (fun z : ℝ => z + d) hmuVal)
      change -(3 * delta) ≤ H (j p) - (k + d) ∧
        H (j p) - (k + d) ≤ 3 * delta at hh
      linarith only [hh.2, hpMax, hgapHi, hdelta]
  clear hwslo hwshi hwsroot hwmlo hwmhi hwmroot hsigma hm_point hm_source hm_zero
    hm hmi hm_height m hpCoordinates hpsource hqs _hSmooth _hklo _hkhi _hmulo
    _hqm _hks hmum hclass _hNoncritical _hRegular hqsEq hvmNorm hmuVal hNorm hwmrad vm
  clear_value psi k
  obtain ⟨f, hf, hfpsi, hfnz⟩ := exists_sphere_collar_defining_function psi hpsi
  let Ubase := (U ∩ {y : E3 | |H y - c| < 4 * delta}) \ (j '' Dc (rho / 4))
  have hinner : IsCompact (j '' Dc (rho / 4)) :=
    (hgeom _ (by positivity) (by linarith only [hrho])).2.1.image hj
  have hUbase : IsOpen Ubase :=
    (hU.inter (isOpen_lt ((H.continuous.sub continuous_const).abs) continuous_const)).sdiff
      hinner.isClosed
  have hKbase : j '' Ksrc ⊆ Ubase := by
    rintro y ⟨p, hp, rfl⟩
    refine ⟨⟨hjU p, ?_⟩, ?_⟩
    · change |H (j p) - c| < 4 * delta
      have hh : |H (j p) - c| ≤ 3 * delta := hp.1
      linarith only [hh, hdelta]
    rintro ⟨z, hz, hzp⟩
    have hzp' := hji hzp
    subst z
    obtain ⟨s, hs, hsp⟩ := hz
    apply hp.2
    refine ⟨s, ?_, hsp⟩
    change r2 s < (rho / 2) ^ 2
    change r2 s ≤ (rho / 4) ^ 2 at hs
    nlinarith only [hs, hrho2]
  have hgrad (y : E3) (hy : y ∈ U) : gradient f y ≠ 0 := by
    intro hz
    apply hfnz y hy
    rw [← toDual_gradient, hz, map_zero]
  have hproj : ∀ y ∈ j '' Ksrc,
      ⟪u, y⟫_ℝ ∈ tsupport (fun _ : ℝ => (1 : ℝ)) →
        tangentHeightVector (gradient f y) u ≠ 0 := by
    rintro y ⟨p, hp, rfl⟩ _
    exact tangentHeightVector_ne_zero_of_heightCross _ _
      (collar_regular_height_cross_ne_zero psi hpsi f hf hfpsi hfnz u p (hreg p hp))
  obtain ⟨F0, hF0, hF0c, hF0s, hF0f, hF0H⟩ :=
    exists_compact_height_band_field (hKsrc.image hj) hUbase hKbase f
      (hf.mono (fun _ hy => hy.1.1)) (fun y hy => hgrad y hy.1.1)
      u (fun _ => 1) contDiff_const hproj
  simp only [hu] at hF0H
  obtain ⟨epsi, hepsi, hepsis, hepsit, hepsii⟩ := exists_collar_chart psi hpsi
  let M := N.toHomeomorph.toOpenPartialHomeomorph.trans e.symm
  let C := M.prod (OpenPartialHomeomorph.refl ℝ)
  let G := C.trans epsi
  have hMs : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ M M.source :=
    heismooth.comp N.contDiff.contMDiff.contMDiffOn (fun _ hs => hs.2)
  have hMi : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ M.symm M.target :=
    N.symm.contDiff.contMDiff.comp_contMDiffOn (hesmooth.mono inter_subset_left)
  have hCs : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod 𝓘(ℝ, ℝ))
      ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ C C.source := hMs.prodMap contMDiff_id.contMDiffOn
  have hCi : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ))
      (𝓘(ℝ, ℝ × ℝ).prod 𝓘(ℝ, ℝ)) ∞ C.symm C.target := hMi.prodMap contMDiff_id.contMDiffOn
  have hepsif : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E3) ∞ epsi epsi.source := by
    rw [hepsis, hepsi]
    exact hpsi.1
  have hGs : ContDiffOn ℝ ∞ G G.source := by
    have h := hepsif.comp (hCs.mono inter_subset_left) (fun _ hw => hw.2)
    rw [← modelWithCornersSelf_prod] at h
    rw [chartedSpaceSelf_prod] at h
    exact h.contDiffOn
  have hGi : ContDiffOn ℝ ∞ G.symm G.target := by
    have h := hCi.comp (hepsii.mono inter_subset_left) (fun _ hy => hy.2)
    rw [← modelWithCornersSelf_prod] at h
    rw [chartedSpaceSelf_prod] at h
    exact h.contDiffOn
  have hGform (w : (ℝ × ℝ) × ℝ) : G w = psi (e.symm (N w.1), w.2) :=
    congrFun hepsi _
  have hGnative (w : (ℝ × ℝ) × ℝ) (hw : w ∈ G.source) : N w.1 ∈ e.target := hw.1.1.2
  have hGcollar (w : (ℝ × ℝ) × ℝ) (hw : w ∈ G.source) : w.2 ∈ Ioo (-1 : ℝ) 1 := by
    have ht := hw.2
    rw [hepsis] at ht
    exact ht.2
  have hGmem (s : ℝ × ℝ) (r : ℝ) (hs : N s ∈ e.target)
      (hr : r ∈ Ioo (-1 : ℝ) 1) : (s, r) ∈ G.source := by
    refine ⟨⟨⟨mem_univ _, hs⟩, mem_univ _⟩, ?_⟩
    rw [hepsis]
    exact ⟨mem_univ _, hr⟩
  have hGtU : G.target ⊆ U := by
    intro y hy
    let w := G.symm y
    refine ⟨(e.symm (N w.1), w.2), ⟨mem_univ _, hGcollar w (G.map_target hy)⟩, ?_⟩
    exact (hGform w).symm.trans (G.right_inv hy)
  have hGf (w : (ℝ × ℝ) × ℝ) (hw : w ∈ G.source) : f (G w) = w.2 := by
    rw [hGform]
    exact hfpsi _ ⟨mem_univ _, hGcollar w hw⟩
  have hGH (s : ℝ × ℝ) (hs : N s ∈ e.target) : H (G (s, 0)) = c + s.1 ^ 2 - s.2 ^ 2 := by
    have hh := heheight d (e.symm (N s)) (e.map_target hs)
    rw [e.right_inv hs] at hh
    rw [← hLevel] at hh
    rw [hGform]
    change H (j (e.symm (N s))) = _
    change H (j (e.symm (N s))) = c - (N s).1 ^ 2 + (N s).2 ^ 2 at hh
    linarith only [hh, (hN s).2.2]
  clear_value G
  clear hMs hMi hCs hCi hepsif hepsii hepsi hepsis hepsit C M epsi hLevel hNative heheight
  let X : ((ℝ × ℝ) × ℝ) → ((ℝ × ℝ) × ℝ) := fun w =>
    ((1 / (4 * w.1.1), -1 / (4 * w.1.2)), 0)
  let Ax : Set ((ℝ × ℝ) × ℝ) := {w | w.1.1 ≠ 0 ∧ w.1.2 ≠ 0}
  have hAx : IsOpen Ax :=
    (isOpen_ne_fun (by fun_prop) continuous_const).inter
      (isOpen_ne_fun (by fun_prop) continuous_const)
  have hXs : ContDiffOn ℝ ∞ X Ax := by
    exact ((contDiffOn_const.div (by fun_prop)
      (fun w hw => mul_ne_zero (by norm_num) hw.1)).prodMk
      (contDiffOn_const.div (by fun_prop)
        (fun w hw => mul_ne_zero (by norm_num) hw.2))).prodMk contDiffOn_const
  let T : Set E3 := G.target ∩ G.symm ⁻¹' Ax
  have hT : IsOpen T := G.symm.isOpen_inter_preimage hAx
  let W0 : E3 → E3 := fun y => fderiv ℝ G (G.symm y) (X (G.symm y))
  have hW0 : ContDiffOn ℝ ∞ W0 T :=
    ((hGs.fderiv_of_isOpen G.open_source (by simp)).comp
      (hGi.mono inter_subset_left) (fun _ hy => G.map_target hy.1)).clm_apply
      (hXs.comp (hGi.mono inter_subset_left) (fun _ hy => hy.2))
  have hW0f (y : E3) (hy : y ∈ G.target) : fderiv ℝ f y (W0 y) = 0 := by
    let w := G.symm y
    have hw := G.map_target hy
    have hdG := (hGs.contDiffAt (G.open_source.mem_nhds hw)).differentiableAt (by simp)
    have hdf := (hf.contDiffAt (hU.mem_nhds (hGtU hy))).differentiableAt (by simp)
    have heq : (fun z => f (G z)) =ᶠ[𝓝 w] fun z => z.2 := by
      filter_upwards [G.open_source.mem_nhds hw] with z hz
      exact hGf z hz
    have hl := (show HasFDerivAt f (fderiv ℝ f y) (G w) by
      simpa only [w, G.right_inv hy] using hdf.hasFDerivAt).comp w hdG.hasFDerivAt
    have hr := (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ).hasFDerivAt.congr_of_eventuallyEq heq
    have hv := congrArg (fun B : ((ℝ × ℝ) × ℝ) →L[ℝ] ℝ => B (X w)) (hl.unique hr)
    exact hv
  let alpha : E3 → ℝ := fun y => H (W0 y)
  have halpha : ContDiffOn ℝ ∞ alpha T := H.contDiff.comp_contDiffOn hW0
  have hW0H (s : ℝ × ℝ) (hs : N s ∈ e.target) (hx : s.1 ≠ 0) (hy : s.2 ≠ 0) :
      alpha (G (s, 0)) = 1 := by
    have hw := hGmem s 0 hs (by norm_num)
    let v : ℝ × ℝ := (1 / (4 * s.1), -1 / (4 * s.2))
    have hline : HasDerivAt (fun t : ℝ => (s + t • v, (0 : ℝ))) (v, 0) 0 := by
      simpa using ((hasDerivAt_const (0 : ℝ) s).add
        ((hasDerivAt_id (0 : ℝ)).smul_const v)).prodMk (hasDerivAt_const (0 : ℝ) (0 : ℝ))
    have hdG := (hGs.contDiffAt (G.open_source.mem_nhds hw)).differentiableAt (by simp)
    have hdGl : HasFDerivAt G (fderiv ℝ G (s, 0)) (s + (0 : ℝ) • v, 0) := by
      simpa using hdG.hasFDerivAt
    have hl : HasDerivAt (fun t : ℝ => H (G (s + t • v, 0)))
        (H (fderiv ℝ G (s, 0) (v, 0))) 0 := by
      convert! H.hasFDerivAt.comp_hasDerivAt 0
        (hdGl.comp_hasDerivAt (f := fun t : ℝ => (s + t • v, (0 : ℝ))) 0 hline) using 1
    have hx' : HasDerivAt (fun t : ℝ => s.1 + t * v.1) v.1 0 := by
      simpa using ((hasDerivAt_id 0).mul_const v.1).const_add s.1
    have hy' : HasDerivAt (fun t : ℝ => s.2 + t * v.2) v.2 0 := by
      simpa using ((hasDerivAt_id 0).mul_const v.2).const_add s.2
    have hp : HasDerivAt (fun t : ℝ => c + (s.1 + t * v.1) ^ 2 - (s.2 + t * v.2) ^ 2)
        (2 * s.1 * v.1 - 2 * s.2 * v.2) 0 := by
      convert! ((hx'.pow 2).const_add c).sub (hy'.pow 2) using 1
      norm_num
    have hnear : ∀ᶠ t : ℝ in 𝓝 0, (s + t • v, (0 : ℝ)) ∈ G.source :=
      hline.continuousAt.eventually (by simpa using G.open_source.mem_nhds hw)
    have heq : (fun t : ℝ => H (G (s + t • v, 0))) =ᶠ[𝓝 0]
        fun t => c + (s.1 + t * v.1) ^ 2 - (s.2 + t * v.2) ^ 2 := by
      filter_upwards [hnear] with t ht
      exact hGH _ (hGnative _ ht)
    change H (fderiv ℝ G (G.symm (G (s, 0))) (X (G.symm (G (s, 0))))) = 1
    rw [G.left_inv hw]
    change H (fderiv ℝ G (s, 0) (v, 0)) = 1
    rw [hl.unique (hp.congr_of_eventuallyEq heq)]
    dsimp [v]
    field_simp [hx, hy]
    ring
  let K0 : Set (ℝ × ℝ) := {s | (7 * rho / 8) ^ 2 ≤ r2 s ∧
    r2 s ≤ (9 * rho / 8) ^ 2 ∧ |s.1 ^ 2 - s.2 ^ 2| ≤ 5 * delta / 2}
  have hK0closed : IsClosed K0 :=
    (isClosed_le continuous_const hrs.continuous).inter
      ((isClosed_le hrs.continuous continuous_const).inter
        (isClosed_le ((continuous_fst.pow 2).sub (continuous_snd.pow 2)).abs continuous_const))
  have hK0 : IsCompact K0 :=
    (morseRadialDisc_geometry (9 * rho / 8) (by positivity)).2.1.of_isClosed_subset
      hK0closed (fun _ hs => hs.2.1)
  have hK0native (s : ℝ × ℝ) (hs : s ∈ K0) : N s ∈ e.target := by
    apply hmorse
    change (N s).1 ^ 2 + (N s).2 ^ 2 < (2 * R) ^ 2
    rw [(hN s).2.1]
    have hh := hs.2.1
    dsimp only [r2, rho, rhoN] at hh
    nlinarith only [hh, sq_pos_of_pos hR]
  have hK0axes (s : ℝ × ℝ) (hs : s ∈ K0) : s.1 ≠ 0 ∧ s.2 ≠ 0 := by
    obtain ⟨hhlo, hhhi⟩ := abs_le.mp hs.2.2
    have hl := hs.1
    dsimp [r2] at hl
    constructor <;> intro hz
    · rw [hz] at hl hhlo hhhi
      nlinarith only [hl, hhlo, hhhi, hd, hrho2]
    · rw [hz] at hl hhlo hhhi
      nlinarith only [hl, hhlo, hhhi, hd, hrho2]
  let Kwall : Set E3 := (fun s : ℝ × ℝ => G (s, 0)) '' K0
  have hKwall : IsCompact Kwall := hK0.image_of_continuousOn
    (hGs.continuousOn.comp (by fun_prop) (fun s hs => hGmem s 0 (hK0native s hs) (by norm_num)))
  let Vrad := G.target ∩ G.symm ⁻¹' {w : (ℝ × ℝ) × ℝ |
    (3 * rho / 4) ^ 2 < r2 w.1 ∧ r2 w.1 < (5 * rho / 4) ^ 2}
  have hVrad : IsOpen Vrad := G.symm.isOpen_inter_preimage
    ((isOpen_lt continuous_const (hrs.continuous.comp continuous_fst)).inter
      (isOpen_lt (hrs.continuous.comp continuous_fst) continuous_const))
  let O := (T ∩ alpha ⁻¹' Ioi (1 / 2)) ∩
    (Vrad ∩ {y : E3 | |H y - c| < 3 * delta})
  have hO : IsOpen O :=
    (halpha.continuousOn.isOpen_inter_preimage hT isOpen_Ioi).inter
      (hVrad.inter (isOpen_lt ((H.continuous.sub continuous_const).abs) continuous_const))
  have hKwallO : Kwall ⊆ O := by
    rintro y ⟨s, hs, rfl⟩
    have hn := hK0native s hs
    have hw := hGmem s 0 hn (by norm_num)
    have hxy := hK0axes s hs
    refine ⟨⟨⟨G.map_source hw, ?_⟩, ?_⟩, ⟨⟨G.map_source hw, ?_⟩, ?_⟩⟩
    · change (G.symm (G (s, 0))).1.1 ≠ 0 ∧ (G.symm (G (s, 0))).1.2 ≠ 0
      rw [G.left_inv hw]
      exact hxy
    · change 1 / 2 < alpha (G (s, 0))
      rw [hW0H s hn hxy.1 hxy.2]
      norm_num
    · change (3 * rho / 4) ^ 2 < r2 (G.symm (G (s, 0))).1 ∧ _
      rw [G.left_inv hw]
      constructor <;> nlinarith only [hs.1, hs.2.1, hrho2]
    · change |H (G (s, 0)) - c| < 3 * delta
      rw [hGH s hn]
      have heq : c + s.1 ^ 2 - s.2 ^ 2 - c = s.1 ^ 2 - s.2 ^ 2 := by ring
      rw [heq]
      linarith only [hs.2.2, hdelta]
  have hOU : O ⊆ Ubase := by
    intro y hy
    have hyt := hy.1.1.1
    have hw := G.map_target hyt
    have hheight : |H y - c| < 3 * delta := hy.2.2
    refine ⟨⟨hGtU hyt, ?_⟩, ?_⟩
    · change |H y - c| < 4 * delta
      linarith only [hheight, hdelta]
    rintro ⟨p, hp, hpy⟩
    obtain ⟨z, hz, rfl⟩ := hp
    have hzt := hBtarget (rho / 4) (by positivity) (by linarith only [hrho]) hz
    have he : psi (e.symm (N (G.symm y).1), (G.symm y).2) =
        psi (e.symm z, 0) :=
      (hGform (G.symm y)).symm.trans ((G.right_inv hyt).trans hpy.symm)
    have hleft : (e.symm (N (G.symm y).1), (G.symm y).2) ∈
        (univ ×ˢ Ioo (-1) 1 : Set (UnitTwoSphere × ℝ)) :=
      ⟨mem_univ _, hGcollar (G.symm y) hw⟩
    have hright : (e.symm z, (0 : ℝ)) ∈
        (univ ×ˢ Ioo (-1) 1 : Set (UnitTwoSphere × ℝ)) := ⟨mem_univ _, by norm_num⟩
    have hpairs := hpsi.2.1 hleft hright he
    have hcoords := congrArg e (congrArg Prod.fst hpairs)
    rw [e.right_inv (hGnative _ hw), e.right_inv hzt] at hcoords
    have hn := (hN (G.symm y).1).2.1
    rw [hcoords] at hn
    have hl := hy.2.1.2.1
    dsimp [r2] at hz hl
    nlinarith only [hz, hl, hn, hrho2]
  let W : E3 → E3 := fun y => (alpha y)⁻¹ • W0 y
  have ha0 (y : E3) (hy : y ∈ O) : alpha y ≠ 0 := by
    have hh : 1 / 2 < alpha y := hy.1.2
    exact ne_of_gt (lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hh)
  have hWs : ContDiffOn ℝ ∞ W O :=
    ((halpha.mono (fun _ hy => hy.1.1)).inv ha0).smul (hW0.mono (fun _ hy => hy.1.1))
  have hWH (y : E3) (hy : y ∈ O) : H (W y) = 1 := by
    change H ((alpha y)⁻¹ • W0 y) = 1
    rw [map_smul]
    exact inv_mul_cancel₀ (ha0 y hy)
  have hWf (y : E3) (hy : y ∈ O) : fderiv ℝ f y (W y) = 0 := by
    change fderiv ℝ f y ((alpha y)⁻¹ • W0 y) = 0
    rw [map_smul, hW0f y hy.1.1.1, smul_zero]
  obtain ⟨theta, htheta, hthetac, hthetas, hthetanear, _⟩ :=
    exists_compact_smooth_cutoff hKwall hO hKwallO
  let F : E3 → E3 := fun y => (1 - theta y) • F0 y + theta y • W y
  have hF : ContDiff ℝ ∞ F :=
    ((contDiff_const.sub htheta).smul hF0).add (contDiff_cutoff_smul hO theta htheta hthetas W hWs)
  have hFc : HasCompactSupport F := by
    have hleft : HasCompactSupport (fun y : E3 => (1 - theta y) • F0 y) :=
      hF0c.smul_left (f := fun y : E3 => 1 - theta y)
    have hright : HasCompactSupport (fun y : E3 => theta y • W y) :=
      hthetac.smul_right (f' := W)
    exact hleft.add hright
  have hFs : tsupport F ⊆ Ubase := by
    have hs : Function.support F ⊆ tsupport F0 ∪ tsupport theta := by
      intro y hy
      by_contra hn
      have hparts := not_or.mp hn
      apply hy
      simp only [F, image_eq_zero_of_notMem_tsupport hparts.1,
        image_eq_zero_of_notMem_tsupport hparts.2, smul_zero, zero_smul, add_zero]
    exact (closure_minimal hs ((isClosed_tsupport F0).union (isClosed_tsupport theta))).trans
      (union_subset hF0s (hthetas.trans hOU))
  have hFf (y : E3) : fderiv ℝ f y (F y) = 0 := by
    change fderiv ℝ f y ((1 - theta y) • F0 y + theta y • W y) = 0
    rw [map_add, map_smul, hF0f y, smul_zero, zero_add, map_smul]
    by_cases ht : theta y = 0
    · rw [ht, zero_smul]
    · rw [hWf y (hthetas (subset_tsupport theta ht)), smul_zero]
  have hFH (p : UnitTwoSphere) (hp : |H (j p) - c| ≤ 3 * delta) (hpo : p ∉ Do (rho / 2)) :
      H (F (j p)) = 1 := by
    have hbase := hF0H (j p) ⟨p, ⟨hp, hpo⟩, rfl⟩
    change H (F0 (j p)) = 1 at hbase
    change H ((1 - theta (j p)) • F0 (j p) + theta (j p) • W (j p)) = 1
    rw [map_add, map_smul, map_smul, hbase]
    by_cases ht : theta (j p) = 0
    · simp only [ht, sub_zero, one_smul, zero_smul, add_zero]
    · rw [hWH _ (hthetas (subset_tsupport theta ht))]
      change (1 - theta (j p)) * 1 + theta (j p) * 1 = 1
      ring
  have hFonWall (y : E3) (hy : y ∈ Kwall) : F y = W0 y := by
    obtain ⟨s, hs, rfl⟩ := hy
    have ht : theta (G (s, 0)) = 1 := subset_of_mem_nhdsSet hthetanear ⟨s, hs, rfl⟩
    have ha := hW0H s (hK0native s hs) (hK0axes s hs).1 (hK0axes s hs).2
    simp only [F, W, ht, ha, sub_self, zero_smul, one_smul, inv_one, zero_add]
  have hsg (i : Fin 4) : sx i ^ 2 = 1 ∧ sy i ^ 2 = 1 ∧ sx i ≠ 0 ∧ sy i ≠ 0 := by
    fin_cases i <;> norm_num [sx, sy]
  let V : Set (ℝ × ℝ) := Ioo (-3 * delta) (3 * delta) ×ˢ Ioo (-(1 / 4)) (1 / 4)
  have hrad (p : ℝ × ℝ) (hp : p ∈ V) :
      (3 * rho / 4) ^ 2 < rho ^ 2 * (1 + p.2) ^ 2 ∧
      rho ^ 2 * (1 + p.2) ^ 2 < (5 * rho / 4) ^ 2 := by
    have hl := mul_lt_mul_of_pos_left
      ((sq_lt_sq₀ (by norm_num : (0 : ℝ) ≤ 3 / 4) (by linarith only [hp.2.1])).mpr
        (by linarith only [hp.2.1] : (3 : ℝ) / 4 < 1 + p.2)) hrho2
    have hu := mul_lt_mul_of_pos_left
      ((sq_lt_sq₀ (by linarith only [hp.2.1]) (by norm_num : (0 : ℝ) ≤ 5 / 4)).mpr
        (by linarith only [hp.2.2] : 1 + p.2 < (5 : ℝ) / 4)) hrho2
    constructor <;> nlinarith only [hl, hu]
  have hroots (p : ℝ × ℝ) (hp : p ∈ V) :
      0 < (rho ^ 2 * (1 + p.2) ^ 2 + p.1) / 2 ∧
      0 < (rho ^ 2 * (1 + p.2) ^ 2 - p.1) / 2 := by
    have hh := hrad p hp
    constructor <;> nlinarith only [hp.1.1, hp.1.2, hh.1, hd]
  have hxi (i : Fin 4) (p : ℝ × ℝ) (hp : p ∈ V) :
      r2 (xi i p) = rho ^ 2 * (1 + p.2) ^ 2 ∧
      (xi i p).1 ^ 2 - (xi i p).2 ^ 2 = p.1 := by
    have hx := Real.sq_sqrt (hroots p hp).1.le
    have hy := Real.sq_sqrt (hroots p hp).2.le
    constructor <;> dsimp [r2, xi] <;>
      rw [mul_pow, mul_pow, (hsg i).1, (hsg i).2.1] <;> nlinarith only [hx, hy]
  have hxit (i : Fin 4) (p : ℝ × ℝ) (hp : p ∈ V) : N (xi i p) ∈ e.target := by
    apply hmorse
    change (N (xi i p)).1 ^ 2 + (N (xi i p)).2 ^ 2 < (2 * R) ^ 2
    rw [(hN _).2.1]
    change r2 (xi i p) < (2 * R) ^ 2
    rw [(hxi i p hp).1]
    have hh := (hrad p hp).2
    dsimp only [rho, rhoN] at hh ⊢
    nlinarith only [hh, sq_pos_of_pos hR]
  have hclosedV (a t : ℝ) (ha : |a| < 1 / 8) (ht : |t| ≤ 2 * delta) : (t, a) ∈ V := by
    have haa := abs_lt.mp ha
    have htt := abs_le.mp ht
    exact ⟨⟨by linarith only [htt.1, hdelta], by linarith only [htt.2, hdelta]⟩,
      ⟨by linarith only [haa.1], by linarith only [haa.2]⟩⟩
  have hq (i : Fin 4) (a : ℝ) (ha : |a| < 1 / 8) (t : ℝ) (ht : |t| ≤ 2 * delta) :
      q i (t, a) ∈ e.source ∧ H (j (q i (t, a))) = c + t ∧
      r2 (e (q i (t, a))) = rho ^ 2 * (1 + a) ^ 2 := by
    have hv := hclosedV a t ha ht
    have hn := hxit i (t, a) hv
    refine ⟨e.map_target hn, ?_, ?_⟩
    · have hh := hGH (xi i (t, a)) hn
      rw [hGform] at hh
      change H (j (q i (t, a))) = c + (xi i (t, a)).1 ^ 2 - (xi i (t, a)).2 ^ 2 at hh
      linarith only [hh, (hxi i (t, a) hv).2]
    · change r2 (e (e.symm (N (xi i (t, a))))) = _
      rw [e.right_inv hn]
      exact (hN _).2.1.trans (hxi i (t, a) hv).1
  have hxiK (i : Fin 4) (a : ℝ) (ha : |a| < 1 / 8) (t : ℝ) (ht : |t| ≤ 2 * delta) :
      xi i (t, a) ∈ K0 := by
    have hv := hclosedV a t ha ht
    have haa := abs_lt.mp ha
    have hl := mul_lt_mul_of_pos_left
      ((sq_lt_sq₀ (by norm_num : (0 : ℝ) ≤ 7 / 8) (by linarith only [haa.1])).mpr
        (by linarith only [haa.1] : (7 : ℝ) / 8 < 1 + a)) hrho2
    have hu := mul_lt_mul_of_pos_left
      ((sq_lt_sq₀ (by linarith only [haa.1]) (by norm_num : (0 : ℝ) ≤ 9 / 8)).mpr
        (by linarith only [haa.2] : 1 + a < (9 : ℝ) / 8)) hrho2
    change (7 * rho / 8) ^ 2 ≤ r2 (xi i (t, a)) ∧ _
    rw [(hxi i (t, a) hv).1, (hxi i (t, a) hv).2]
    exact ⟨by nlinarith only [hl], by nlinarith only [hu],
      by linarith only [ht, hdelta]⟩
  have hsigned (e x : ℝ) (he : e ^ 2 = 1) (hx : 0 < e * x) : e * Real.sqrt (x ^ 2) = x := by
    rcases sq_eq_one_iff.mp he with rfl | rfl
    · simp only [one_mul] at hx ⊢
      exact Real.sqrt_sq hx.le
    · have hn : x < 0 := by linarith only [hx]
      rw [Real.sqrt_sq_eq_abs, abs_of_neg hn]
      ring
  have hwall (t : ℝ) (ht : |t| ≤ 2 * delta) :
      {p : UnitTwoSphere | p ∈ Dc rho \ Do rho ∧ H (j p) = c + t} =
        range (fun i => q i (t, 0)) := by
    ext p
    constructor
    · rintro ⟨⟨hpc, hpo⟩, hph⟩
      obtain ⟨hp, hpr⟩ := (hDcMem rho hrho (by linarith only [hrho]) p).mp hpc
      have hpr' : r2 (e p) = rho ^ 2 := le_antisymm hpr (le_of_not_gt (fun hh =>
        hpo ((hDoMem rho hrho (by linarith only [hrho]) p).mpr ⟨hp, hh⟩)))
      let s := N (e p)
      have hNs : N s = e p := (hN _).1
      have hsn : N s ∈ e.target := hNs.symm ▸ e.map_source hp
      have hsr : s.1 ^ 2 + s.2 ^ 2 = rho ^ 2 := (hN _).2.1.trans hpr'
      have hsh : s.1 ^ 2 - s.2 ^ 2 = t := by
        have hh := hGH s hsn
        rw [hGform, hNs, e.left_inv hp] at hh
        change H (j p) = c + s.1 ^ 2 - s.2 ^ 2 at hh
        linarith only [hh, hph]
      have hx2 : s.1 ^ 2 = (rho ^ 2 + t) / 2 := by nlinarith only [hsr, hsh]
      have hy2 : s.2 ^ 2 = (rho ^ 2 - t) / 2 := by nlinarith only [hsr, hsh]
      obtain ⟨httlo, htthi⟩ := abs_le.mp ht
      have hxn : s.1 ≠ 0 := sq_pos_iff.mp (by nlinarith only [hx2, httlo, hd, hrho2] : 0 < s.1 ^ 2)
      have hyn : s.2 ≠ 0 := sq_pos_iff.mp (by nlinarith only [hy2, htthi, hd, hrho2] : 0 < s.2 ^ 2)
      have hi : ∃ i : Fin 4, 0 < sx i * s.1 ∧ 0 < sy i * s.2 := by
        rcases lt_or_gt_of_ne hxn with hx | hx
        · rcases lt_or_gt_of_ne hyn with hy | hy
          · exact ⟨2, by simpa [sx, sy] using And.intro hx hy⟩
          · exact ⟨1, by simpa [sx, sy] using And.intro hx hy⟩
        · rcases lt_or_gt_of_ne hyn with hy | hy
          · exact ⟨3, by simpa [sx, sy] using And.intro hx hy⟩
          · exact ⟨0, by simpa [sx, sy] using And.intro hx hy⟩
      obtain ⟨i, his⟩ := hi
      have heq : xi i (t, 0) = s := by
        apply Prod.ext
        · change sx i * Real.sqrt ((rho ^ 2 * (1 + 0) ^ 2 + t) / 2) = s.1
          simp only [add_zero, one_pow, mul_one]
          rw [← hx2]
          exact hsigned _ _ (hsg i).1 his.1
        · change sy i * Real.sqrt ((rho ^ 2 * (1 + 0) ^ 2 - t) / 2) = s.2
          simp only [add_zero, one_pow, mul_one]
          rw [← hy2]
          exact hsigned _ _ (hsg i).2.1 his.2
      refine ⟨i, ?_⟩
      change e.symm (N (xi i (t, 0))) = p
      rw [heq, hNs, e.left_inv hp]
    · rintro ⟨i, rfl⟩
      have hp := hq i 0 (by norm_num) t ht
      have hr : r2 (e (q i (t, 0))) = rho ^ 2 := by simpa using hp.2.2
      refine ⟨⟨(hDcMem rho hrho (by linarith only [hrho]) _).mpr ⟨hp.1, hr.le⟩, ?_⟩, hp.2.1⟩
      intro hh
      have hh' := ((hDoMem rho hrho (by linarith only [hrho]) _).mp hh).2
      rw [hr] at hh'
      exact (lt_irrefl _ hh')
  refine ⟨f, F, hf, hfpsi, hF, hFc, hFs, hFf, hFH,
    hgeom, hq, hwall, ?_⟩
  intro i a ha t ht
  have hv := hclosedV a t ha ht
  have hp := hroots (t, a) hv
  have hp1 := (Real.sqrt_pos.mpr hp.1).ne'
  have hp2 := (Real.sqrt_pos.mpr hp.2).ne'
  have dp : HasDerivAt (fun v : ℝ => (rho ^ 2 * (1 + a) ^ 2 + v) / 2) (1 / 2) t :=
    ((hasDerivAt_id t).const_add _).div_const 2
  have dm : HasDerivAt (fun v : ℝ => (rho ^ 2 * (1 + a) ^ 2 - v) / 2) (-1 / 2) t :=
    ((hasDerivAt_id t).const_sub _).div_const 2
  have dx := HasDerivAt.const_mul (sx i) (dp.sqrt hp.1.ne')
  have dy := HasDerivAt.const_mul (sy i) (dm.sqrt hp.2.ne')
  have hrecip (sg z : ℝ) (hs : sg ^ 2 = 1) (hz : z ≠ 0) :
      1 / (4 * (sg * z)) = sg * (1 / 2 / (2 * z)) := by
    have hn : sg ≠ 0 := by
      intro hn
      simp only [hn, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hs
      norm_num at hs
    field_simp [hn, hz]
    nlinarith only [hs]
  have hxiDer : HasDerivAt (fun v : ℝ => xi i (v, a))
      (1 / (4 * (xi i (t, a)).1), -1 / (4 * (xi i (t, a)).2)) t := by
    convert dx.prodMk dy using 1
    apply Prod.ext
    · exact hrecip (sx i) _ (hsg i).1 hp1
    · simpa only [neg_div, mul_neg] using
        congrArg Neg.neg (hrecip (sy i) _ (hsg i).2.1 hp2)
  have hw := hGmem (xi i (t, a)) 0 (hxit i (t, a) hv) (by norm_num)
  have hdG := (hGs.contDiffAt (G.open_source.mem_nhds hw)).differentiableAt (by simp)
  have hcurve : HasDerivAt (fun v : ℝ => G (xi i (v, a), 0))
      (W0 (G (xi i (t, a), 0))) t := by
    simpa only [Function.comp_def, W0, G.left_inv hw, X] using
      hdG.hasFDerivAt.comp_hasDerivAt t (hxiDer.prodMk (hasDerivAt_const t (0 : ℝ)))
  rw [← hFonWall _ ⟨xi i (t, a), hxiK i a ha t ht, rfl⟩] at hcurve
  have hNform (s : ℝ × ℝ) : N s = (sigma * s.2, sigma * s.1) := rfl
  simpa only [hGform, q, j, hNform] using hcurve

end PoincareConjecture.M25.Topology3D.NestedReferenceLower
