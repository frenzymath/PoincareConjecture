import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsCapEnd
import PoincareConjecture.Proofs.M25.Topology3D.Space3.FieldLocalization
import PoincareConjecture.Proofs.M25.Topology3D.Plane.CircleBoundaryAssembly

set_option autoImplicit false

open Set Metric Filter Function
open scoped ContDiff Manifold Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

local notation "P" => (ℝ × E2)
local notation "CircleDiff" => Diffeomorph (𝓡 1) (𝓡 1) UnitCircle UnitCircle ∞

theorem exists_stackClippedCircleLabels
    (phi : ℝ → CircleDiff) (jL A B jR : ℝ)
    (hLA : jL < A) (hAB : A ≤ B) (hBR : B < jR)
    (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 1)) (𝓡 1) ∞
      (fun p : ℝ × UnitCircle => phi p.1 p.2) (Ioo jL jR ×ˢ univ)) :
    ∃ R : E2 ≃ₗᵢ[ℝ] E2,
      (R = LinearIsometryEquiv.refl ℝ E2 ∨
        R = Complex.orthonormalBasisOneI.repr.symm.trans
          (Complex.conjLIE.trans Complex.orthonormalBasisOneI.repr)) ∧
      ∃ L : ℝ → CircleDiff,
        ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) (𝓡 1) ∞
          (fun p : ℝ × UnitCircle => L p.1 p.2) ∧
        ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) (𝓡 1) ∞
          (fun p : ℝ × UnitCircle => (L p.1).symm p.2) ∧
        (∀ z ∈ Icc A B, ∀ q : UnitCircle,
          L z q = phi z ⟨R (q : E2), by
            simpa only [mem_sphere_zero_iff_norm, R.norm_map] using q.property⟩) ∧
        (∀ z ∉ Ioo jL jR, ∀ q : UnitCircle, L z q = q) := by
  classical
  let : Fact (Module.finrank ℝ E2 = 1 + 1) := ⟨by simp [E2]⟩
  let e : ℂ ≃ₗᵢ[ℝ] E2 := Complex.orthonormalBasisOneI.repr
  have hJ : jL < jR := hLA.trans_le hAB |>.trans hBR
  have hsub : Icc A B ⊆ Ioo jL jR :=
    (Icc_subset_Ioo_iff hAB).mpr ⟨hLA, hBR⟩
  obtain ⟨chi, hchi, _hcompact, hsupport, hnear, hrange⟩ :=
    exists_compact_smooth_cutoff isCompact_Icc isOpen_Ioo hsub
  have hone (z : ℝ) (hz : z ∈ Icc A B) : chi z = 1 :=
    (eventually_nhdsSet_iff_forall.mp hnear z hz).self_of_nhds
  have hzero (z : ℝ) (hz : z ∉ Ioo jL jR) : chi z = 0 := by
    by_contra hn
    exact hz (hsupport (subset_closure hn))
  let z0 := (jL + jR) / 2
  have hz0 : z0 ∈ Ioo jL jR := ⟨by dsimp [z0]; linarith, by dsimp [z0]; linarith⟩
  let beta : ℝ → ℝ := fun z => (1 - chi z) * z0 + chi z * z
  have hbeta : ContDiff ℝ ∞ beta :=
    ((contDiff_const.sub hchi).mul contDiff_const).add (hchi.mul contDiff_id)
  have hbetaJ (z : ℝ) : beta z ∈ Ioo jL jR := by
    by_cases hz : chi z = 0
    · simpa only [beta, hz, sub_zero, one_mul, zero_mul, add_zero] using hz0
    · have hzJ : z ∈ Ioo jL jR := hsupport (subset_closure hz)
      exact (convex_Ioo jL jR) hz0 hzJ
        (sub_nonneg.mpr (hrange z).2) (hrange z).1 (by ring)
  have hbetafix (z : ℝ) (hz : z ∈ Icc A B) : beta z = z := by
    simp only [beta, hone z hz, sub_self, zero_mul, one_mul, zero_add]
  let f : ℝ → UnitCircle → UnitCircle := fun z q => phi (beta z) q
  have hfn : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) (𝓡 1) ∞
      (fun p : ℝ × UnitCircle => f p.1 p.2) :=
    hf.comp_contMDiff
      ((hbeta.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd)
      (fun p => ⟨hbetaJ p.1, mem_univ _⟩)
  have hfc : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, E2) ∞
      (fun p : ℝ × UnitCircle => (f p.1 p.2 : E2)) :=
    (contMDiff_coe_sphere (E := E2) (n := 1)).comp hfn
  have hfi (z : ℝ) (q : UnitCircle) : Injective
      (mfderiv (𝓡 1) 𝓘(ℝ, E2) (fun q => (f z q : E2)) q) := by
    have hi : ContMDiff (𝓡 1) 𝓘(ℝ, E2) ∞ (fun q : UnitCircle => (q : E2)) :=
      contMDiff_coe_sphere
    have hd := ((phi (beta z)).toOpenPartialHomeomorph_mdifferentiable
      (by simp)).mfderiv_injective (mem_univ q)
    have hinc : Injective (mfderiv (𝓡 1) 𝓘(ℝ, E2)
        (fun q : UnitCircle => (q : E2)) (f z q)) := by
      intro v w hvw
      exact injective_mvfderiv_subtypeVal_sphere (f z q)
        (congrArg (NormedSpace.fromTangentSpace (𝕜 := ℝ) (f z q : E2)) hvw)
    change Injective (mfderiv (𝓡 1) 𝓘(ℝ, E2)
      ((fun q : UnitCircle => (q : E2)) ∘ (phi (beta z))) q)
    rw [mfderiv_comp q (hi.mdifferentiable (by simp) _)
      ((phi (beta z)).mdifferentiable (by simp) q)]
    exact hinc.comp hd
  let gamma : ℝ × ℝ → E2 := fun p => f p.1 (sphereCircleParameter e p.2)
  have hgamma : ContDiff ℝ ∞ gamma :=
    contDiff_curveFamily_circleParameter e (fun z q => (f z q : E2)) hfc
  have hnorm (p : ℝ × ℝ) : ‖gamma p‖ = 1 := norm_eq_of_mem_sphere _
  have hnonzero (z t : ℝ) : deriv (fun s => gamma (z, s)) t ≠ 0 :=
    deriv_curveFamily_circleParameter_ne_zero e (fun z q => (f z q : E2)) hfc z t
      (hfi z (sphereCircleParameter e t))
  obtain ⟨t0, ht0⟩ := surjective_sphereCircleParameter e (f 0 (sphereCircleParameter e 0))
  obtain ⟨B0, hB0, _hB00, hphase⟩ := exists_contDiff_sphere_parameter_lift e gamma
    hgamma hnorm (0, 0) t0 (congrArg Subtype.val ht0)
  let d : ℝ × ℝ → ℝ := fun p => fderiv ℝ B0 p (0, 1)
  have hd : Continuous d :=
    ((hB0.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous
  have hder (z t : ℝ) : HasDerivAt (fun s => B0 (z, s)) (d (z, t)) t :=
    (hB0.differentiable (by simp) (z, t)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_const t z).prodMk (hasDerivAt_id t))
  have hdne (p : ℝ × ℝ) : d p ≠ 0 := by
    intro heq
    have h := (hasDerivAt_sphereCircleParameter_coe e (B0 p)).scomp p.2
      (hder p.1 p.2)
    have he : ((fun s => (sphereCircleParameter e s : E2)) ∘
        fun s => B0 (p.1, s)) = fun s => gamma (p.1, s) :=
      funext (fun s => hphase (p.1, s))
    rw [he, heq, zero_smul] at h
    exact hnonzero p.1 p.2 h.deriv
  have hsign : (∀ p, 0 < d p) ∨ ∀ p, d p < 0 := by
    rcases lt_or_gt_of_ne (hdne (0, 0)) with hneg | hpos
    · right
      intro p
      by_contra hp
      obtain ⟨v, hv⟩ := intermediate_value_univ (0, 0) p hd ⟨hneg.le, le_of_not_gt hp⟩
      exact hdne v hv
    · left
      intro p
      by_contra hp
      obtain ⟨v, hv⟩ := intermediate_value_univ p (0, 0) hd ⟨le_of_not_gt hp, hpos.le⟩
      exact hdne v hv
  let Rc : E2 ≃ₗᵢ[ℝ] E2 := e.symm.trans (Complex.conjLIE.trans e)
  have hRc (t : ℝ) : Rc (sphereCircleParameter e t : E2) =
      (sphereCircleParameter e (-t) : E2) := by
    change e (starRingEnd ℂ (e.symm (e (Circle.exp t : ℂ)))) = e (Circle.exp (-t) : ℂ)
    rw [e.symm_apply_apply, Circle.exp_neg, Circle.coe_inv_eq_conj]
  have hselect : ∃ R : E2 ≃ₗᵢ[ℝ] E2,
      (R = LinearIsometryEquiv.refl ℝ E2 ∨ R = Rc) ∧
      ∃ B' : ℝ × ℝ → ℝ, ContDiff ℝ ∞ B' ∧
        (∀ z t, 0 < deriv (fun s => B' (z, s)) t) ∧
        (∀ z t, (sphereCircleParameter e (B' (z, t)) : E2) =
          (f z ⟨R (sphereCircleParameter e t : E2), by
            rw [mem_sphere_zero_iff_norm, R.norm_map, norm_eq_of_mem_sphere]⟩ : E2)) := by
    rcases hsign with hpos | hneg
    · refine ⟨LinearIsometryEquiv.refl ℝ E2, Or.inl rfl, B0, hB0, ?_, ?_⟩
      · intro z t
        rw [(hder z t).deriv]
        exact hpos (z, t)
      · exact fun z t => hphase (z, t)
    · refine ⟨Rc, Or.inr rfl, fun p => B0 (p.1, -p.2),
        hB0.comp (contDiff_fst.prodMk contDiff_snd.neg), ?_, ?_⟩
      · intro z t
        have hh := (hder z (-t)).comp t (hasDerivAt_id t).neg
        change HasDerivAt (fun s => B0 (z, -s)) (d (z, -t) * -1) t at hh
        change 0 < deriv (fun s => B0 (z, -s)) t
        rw [hh.deriv]
        nlinarith [hneg (z, -t)]
      · intro z t
        rw [hphase]
        apply congrArg (fun q : UnitCircle => (f z q : E2))
        exact Subtype.ext (hRc t).symm
  obtain ⟨R, hR, B', hB', hpos, hBphase⟩ := hselect
  have hper (z t : ℝ) : B' (z, t + 2 * Real.pi) = B' (z, t) + 2 * Real.pi := by
    apply circle_lift_add_period_of_positive e (fun s => B' (z, s))
      (hB'.comp (contDiff_const.prodMk contDiff_id)) (hpos z)
    · intro s
      apply Subtype.ext
      rw [hBphase, hBphase, periodic_sphereCircleParameter e s]
    · intro s t h
      have hh := congrArg Subtype.val h
      rw [hBphase, hBphase] at hh
      apply Subtype.ext
      apply R.injective
      exact congrArg Subtype.val ((phi (beta z)).injective (Subtype.ext hh))
  let D : ℝ × ℝ → ℝ := fun p => (1 - chi p.1) * p.2 + chi p.1 * B' p
  have hD : ContDiff ℝ ∞ D :=
    ((contDiff_const.sub (hchi.comp contDiff_fst)).mul contDiff_snd).add
      ((hchi.comp contDiff_fst).mul hB')
  have hDper (z t : ℝ) : D (z, t + 2 * Real.pi) = D (z, t) + 2 * Real.pi := by
    dsimp only [D]
    rw [hper]
    ring
  have hDpos (z t : ℝ) : 0 < deriv (fun s => D (z, s)) t := by
    have hb : ContDiff ℝ ∞ (fun s => B' (z, s)) :=
      hB'.comp (contDiff_const.prodMk contDiff_id)
    have hh := ((hasDerivAt_id t).const_mul (1 - chi z)).add
      ((hb.differentiable (by simp) t).hasDerivAt.const_mul (chi z))
    change HasDerivAt (fun s => D (z, s))
      ((1 - chi z) * 1 + chi z * deriv (fun s => B' (z, s)) t) t at hh
    rw [hh.deriv, mul_one]
    rcases eq_or_lt_of_le (hrange z).1 with hz | hz
    · rw [← hz]
      norm_num
    · have hp := mul_pos hz (hpos z t)
      linarith [(hrange z).2]
  have hperiod : 0 < 2 * Real.pi := by positivity
  obtain ⟨G, hG, hDG⟩ := exists_smooth_inverse_of_add_period hperiod hD hDper hDpos
  have hp : ContDiff ℝ ∞ (fun s : ℝ => (sphereCircleParameter e s : E2)) :=
    ((contMDiff_coe_sphere (E := E2) (n := 1)).comp
      (contMDiff_sphereCircleParameter e)).contDiff
  have build (H : ℝ × ℝ → ℝ) (hH : ContDiff ℝ ∞ H)
      (hHper : ∀ z t, H (z, t + 2 * Real.pi) = H (z, t) + 2 * Real.pi) :
      ∃ F : ℝ → UnitCircle → UnitCircle,
        ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) (𝓡 1) ∞
          (fun p : ℝ × UnitCircle => F p.1 p.2) ∧
        ∀ z t, F z (sphereCircleParameter e t) = sphereCircleParameter e (H (z, t)) := by
    let gamma' : ℝ → ℝ → E2 := fun z t => sphereCircleParameter e (H (z, t))
    have hg : ContDiff ℝ ∞ (fun p : ℝ × ℝ => gamma' p.1 p.2) := hp.comp hH
    have hgp (z : ℝ) : Periodic (gamma' z) (2 * Real.pi) := by
      intro t
      change (sphereCircleParameter e (H (z, t + 2 * Real.pi)) : E2) = _
      rw [hHper]
      exact congrArg Subtype.val (periodic_sphereCircleParameter e _)
    let f' : ℝ → UnitCircle → E2 := fun z q =>
      periodicCircleCurve (2 * Real.pi) e (gamma' z) q
    have hrep (z t : ℝ) : f' z (sphereCircleParameter e t) =
        (sphereCircleParameter e (H (z, t)) : E2) := by
      simpa only [div_self hperiod.ne', one_mul] using
        periodicCircleCurve_sphereCircleParameter hperiod e (hgp z) t
    have hn (z : ℝ) (q : UnitCircle) : f' z q ∈ sphere (0 : E2) 1 := by
      obtain ⟨t, rfl⟩ := surjective_sphereCircleParameter e q
      rw [hrep]
      exact (sphereCircleParameter e _).property
    let F : ℝ → UnitCircle → UnitCircle := fun z q => ⟨f' z q, hn z q⟩
    refine ⟨F, ?_, fun z t => Subtype.ext (hrep z t)⟩
    exact (contMDiff_periodicCircleCurve_family hperiod e gamma' hg hgp).codRestrict_sphere
      (fun p : ℝ × UnitCircle => hn p.1 p.2)
  obtain ⟨F, hF, hFrep⟩ := build D hD hDper
  obtain ⟨V, hV, hVrep⟩ := build G hG (fun z t => (hDG z t).2.2)
  have hleft (z : ℝ) (q : UnitCircle) : V z (F z q) = q := by
    obtain ⟨t, rfl⟩ := surjective_sphereCircleParameter e q
    rw [hFrep, hVrep, (hDG z t).2.1]
  have hright (z : ℝ) (q : UnitCircle) : F z (V z q) = q := by
    obtain ⟨t, rfl⟩ := surjective_sphereCircleParameter e q
    rw [hVrep, hFrep, (hDG z t).1]
  let L : ℝ → CircleDiff := fun z => {
    toEquiv := { toFun := F z, invFun := V z, left_inv := hleft z, right_inv := hright z }
    contMDiff_toFun := hF.comp (contMDiff_const.prodMk contMDiff_id)
    contMDiff_invFun := hV.comp (contMDiff_const.prodMk contMDiff_id) }
  refine ⟨R, hR, L, hF, hV, ?_, ?_⟩
  · intro z hz q
    obtain ⟨t, rfl⟩ := surjective_sphereCircleParameter e q
    change F z (sphereCircleParameter e t) = _
    rw [hFrep]
    apply Subtype.ext
    simp only [D, hone z hz, sub_self, zero_mul, one_mul, zero_add]
    rw [hBphase]
    change (phi (beta z) _ : E2) = _
    rw [hbetafix z hz]
  · intro z hz q
    obtain ⟨t, rfl⟩ := surjective_sphereCircleParameter e q
    change F z (sphereCircleParameter e t) = _
    rw [hFrep]
    simp only [D, hzero z hz, sub_zero, one_mul, zero_mul, add_zero]

theorem exists_stackCapEndLabels
    {psi : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}
    (C : SurgeryCapTag psi u)
    (c : ℝ → UnitCircle → E2) (c0 c1 jL jR : ℝ)
    (D0 : PlanarSchoenfliesFamilyData c c0 c1)
    (G0 : PlanarFamilyGraphChart D0)
    (hJ : jL < jR) (hJband : Ioo jL jR ⊆ Icc c0 c1)
    (hJcap : Ioo jL jR ⊆
      Ioo (C.cutHeight + C.sign * C.removal - C.scale * C.overlapWidth / 2)
        (C.cutHeight + C.sign * C.removal + C.scale * C.overlapWidth / 2))
    (hfull : ∀ z ∈ Ioo jL jR,
      range (c z) = {x : E2 |
        (heightPlaneCoordinates u).symm (x,z) ∈
          range (fun q : UnitTwoSphere => psi (q,0))}) :
    let T := stackCapEndChart C (LinearIsometryEquiv.refl ℝ E2)
    ∃ phi : ℝ → CircleDiff,
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 1)) (𝓡 1) ∞
        (fun p : ℝ × UnitCircle => phi p.1 p.2)
        (Ioo jL jR ×ˢ univ) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 1)) (𝓡 1) ∞
        (fun p : ℝ × UnitCircle => (phi p.1).symm p.2)
        (Ioo jL jR ×ˢ univ) ∧
      (∀ z ∈ Ioo jL jR, ∀ q : UnitCircle,
        (phi z q : E2) = (G0.chart.symm (T (z,(q : E2)))).2 ∧
        ((phi z).symm q : E2) =
          (T.symm (G0.chart (z,(q : E2)))).2 ∧
        c z (phi z q) = (T (z,(q : E2))).2) ∧
      (∀ z ∉ Ioo jL jR, ∀ q : UnitCircle, phi z q = q) := by
  classical
  let : Fact (Module.finrank ℝ E2 = 1 + 1) := ⟨by simp [E2]⟩
  let e : ℂ ≃ₗᵢ[ℝ] E2 := Complex.orthonormalBasisOneI.repr
  let T := stackCapEndChart C (LinearIsometryEquiv.refl ℝ E2)
  have hTs := stackCapEndChart_spec C (LinearIsometryEquiv.refl ℝ E2)
  have hTf := stackCapEndFiber_spec C (LinearIsometryEquiv.refl ℝ E2)
  have hsource (z : ℝ) (q : UnitCircle) : (z, (q : E2)) ∈ T.source :=
    hTs.2.2.2.2.2.2.1 ⟨mem_univ _, sphere_subset_closedBall q.property⟩
  have hGsource (z : ℝ) (hz : z ∈ Ioo jL jR) (q : UnitCircle) :
      (z, (q : E2)) ∈ G0.chart.source :=
    G0.mem_source (hJband hz)
      (mem_ball_zero_iff.mpr ((norm_eq_of_mem_sphere q).trans_lt G0.one_lt_radius))
  have htube (z : ℝ) (hz : z ∈ Ioo jL jR) (theta : UnitCircle) :
      C.tube ((theta : E2), z) ∈ range (fun q : UnitTwoSphere => psi (q, 0)) := by
    let s := C.cutHeight + C.sign * C.removal
    let v := (z - s) / (C.sign * C.scale)
    have hsign : C.sign ≠ 0 := by
      intro h
      have h' := C.sign_abs
      rw [h, abs_zero] at h'
      norm_num at h'
    have hv : |v| < C.overlapWidth / 2 := by
      dsimp only [v]
      rw [abs_div, abs_mul, C.sign_abs, one_mul, abs_of_pos C.scale_pos,
        div_lt_iff₀ C.scale_pos]
      have hz' := hJcap hz
      rw [abs_lt]
      constructor <;> dsimp [s] <;> nlinarith [hz'.1, hz'.2]
    have hvsmall : |v| < 1 / 4 := by linarith [C.overlap_le]
    have hv1 : 0 < 1 - v ^ 2 := by
      obtain ⟨hlo, hhi⟩ := abs_lt.mp hvsmall
      nlinarith
    let r := Real.sqrt (1 - v ^ 2)
    have hr : 0 < r := Real.sqrt_pos.mpr hv1
    have hrsq : r ^ 2 = 1 - v ^ 2 := Real.sq_sqrt hv1.le
    have hnorm : ‖heightCoordinates.symm (r • (theta : E2), v)‖ = 1 := by
      have hh := heightCoordinates_symm_norm_sq (r • (theta : E2), v)
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, norm_eq_of_mem_sphere,
        mul_one, hrsq] at hh
      nlinarith [norm_nonneg (heightCoordinates.symm (r • (theta : E2), v))]
    let q : UnitTwoSphere :=
      ⟨heightCoordinates.symm (r • (theta : E2), v), mem_sphere_zero_iff_norm.mpr hnorm⟩
    have hcoord : heightCoordinates (q : E3) = (r • (theta : E2), v) :=
      heightCoordinates.apply_symm_apply _
    have hmodel : C.profile.model q = ((theta : E2), v) := by
      have hh := surgeryCapModel_cylinder C.profile.horizontal C.profile.vertical
        C.profile.horizontal_smooth C.profile.vertical_smooth
        (fun z => (C.profile.horizontal_pos z).ne')
        (fun x => (C.profile.vertical_pos x).ne') C.profile.horizontal_near
        C.profile.vertical_far q (by rw [hcoord]; exact hvsmall.le)
      change C.profile.model q = _ at hh
      rw [hcoord, circleDirection_smul theta hr] at hh
      exact hh
    have hvheight : C.cutHeight + C.sign * (C.removal + C.scale * v) = z := by
      dsimp [v, s]
      field_simp [hsign, C.scale_pos.ne']
      ring
    refine ⟨C.sourceChart q, ?_⟩
    change psi (C.sourceChart q, 0) = C.tube ((theta : E2), z)
    rw [C.central_eq q (by rw [hcoord]; linarith [le_abs_self v, C.overlap_pos]),
      SurgeryCapProfile.capMap_apply, hmodel, hvheight]
  have hmatchExists (z : ℝ) (hz : z ∈ Ioo jL jR) (q : UnitCircle) :
      ∃ eta : UnitCircle, G0.chart (z, (eta : E2)) = T (z, (q : E2)) := by
    have hheight : ⟪(u : E3), C.tube ((q : E2), z)⟫_ℝ = z :=
      C.tube_height _ (C.tube_source ⟨sphere_subset_closedBall q.property, mem_univ _⟩)
    have hy : (heightPlaneCoordinates u (C.tube ((q : E2), z))).1 ∈ range (c z) := by
      rw [hfull z hz]
      change (heightPlaneCoordinates u).symm
        ((heightPlaneCoordinates u (C.tube ((q : E2), z))).1, z) ∈
          range (fun q : UnitTwoSphere => psi (q, 0))
      rw [heightPlaneCoordinates_reconstruct u _ z hheight]
      exact htube z hz q
    obtain ⟨eta, heta⟩ := hy
    refine ⟨eta, ?_⟩
    rw [G0.chart_apply, D0.chart_boundary z (hJband hz) eta]
    apply Prod.ext
    · exact (hTs.2.2.2.2.2.2.2.1 _ (hsource z q)).symm
    · exact heta
  have htarget (z : ℝ) (hz : z ∈ Ioo jL jR) (q : UnitCircle) :
      T (z, (q : E2)) ∈ G0.chart.target := by
    obtain ⟨eta, he⟩ := hmatchExists z hz q
    rw [← he]
    exact G0.chart.map_source (hGsource z hz eta)
  have hinverse (z : ℝ) (hz : z ∈ Ioo jL jR) (q : UnitCircle) :
      ∃ eta : UnitCircle, G0.chart.symm (T (z, (q : E2))) = (z, (eta : E2)) ∧
        c z eta = (T (z, (q : E2))).2 := by
    obtain ⟨eta, he⟩ := hmatchExists z hz q
    refine ⟨eta, ?_, ?_⟩
    · rw [← he, G0.chart.left_inv (hGsource z hz eta)]
    · rw [← he, G0.chart_apply, D0.chart_boundary z (hJband hz) eta]
  obtain ⟨zbase, hzbase⟩ := exists_between hJ
  obtain ⟨qbase, _hqbase⟩ := hmatchExists zbase hzbase (sphereCircleParameter e 0)
  let F : ℝ → UnitCircle → UnitCircle := fun z q =>
    unitRadialProjection qbase (G0.chart.symm (T (z, (q : E2)))).2
  have hF (z : ℝ) (hz : z ∈ Ioo jL jR) (q : UnitCircle) :
      (F z q : E2) = (G0.chart.symm (T (z, (q : E2)))).2 ∧
        G0.chart (z, (F z q : E2)) = T (z, (q : E2)) ∧
        c z (F z q) = (T (z, (q : E2))).2 := by
    obtain ⟨eta, hi, hc⟩ := hinverse z hz q
    have he : F z q = eta := by
      change unitRadialProjection qbase (G0.chart.symm (T (z, (q : E2)))).2 = eta
      rw [hi]
      exact unitRadialProjection_apply_coe qbase eta
    rw [he]
    refine ⟨congrArg Prod.snd hi.symm, ?_, hc⟩
    rw [← hi, G0.chart.right_inv (htarget z hz q)]
  have hFsm : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 1)) (𝓡 1) ∞
      (fun p : ℝ × UnitCircle => F p.1 p.2) (Ioo jL jR ×ˢ univ) := by
    apply contMDiffOn_sphere_of_coe (isOpen_Ioo.prod isOpen_univ)
    have hinner : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, P) ∞
        (fun p : ℝ × UnitCircle => T (p.1, (p.2 : E2))) (Ioo jL jR ×ˢ univ) := by
      intro p hp
      have hs := hTs.2.2.2.2.1.contDiffAt (T.open_source.mem_nhds (hsource p.1 p.2))
      exact (hs.contMDiffAt.comp p
        (contMDiffAt_fst.prodMk_space
          (contMDiff_coe_sphere.contMDiffAt.comp p contMDiffAt_snd))).contMDiffWithinAt
    have hout := G0.smooth_symm.contMDiffOn.comp hinner
      (fun p hp => htarget p.1 hp.1 p.2)
    exact (contDiff_snd.contMDiff.comp_contMDiffOn hout).congr
      (fun p hp => (hF p.1 hp.1 p.2).1)
  have hFslice (z : ℝ) (hz : z ∈ Ioo jL jR) :
      ContMDiff (𝓡 1) (𝓡 1) ∞ (F z) := by
    have hp : ContMDiff (𝓡 1) (𝓘(ℝ, ℝ).prod (𝓡 1)) ∞
        (fun q : UnitCircle => (z, q)) := contMDiff_const.prodMk contMDiff_id
    exact ContMDiffOn.comp_contMDiff
      (g := fun p : ℝ × UnitCircle => F p.1 p.2) (f := fun q : UnitCircle => (z, q))
      hFsm hp (fun _ => ⟨hz, mem_univ _⟩)
  have hFinj (z : ℝ) (hz : z ∈ Ioo jL jR) : Injective (F z) := by
    intro q r h
    apply (hTf.2.2 z).2.1
    change (T (z, (q : E2))).2 = (T (z, (r : E2))).2
    rw [← (hF z hz q).2.2, ← (hF z hz r).2.2, h]
  have hFimm (z : ℝ) (hz : z ∈ Ioo jL jR) (q : UnitCircle) :
      Injective (mfderiv (𝓡 1) (𝓡 1) (F z) q) := by
    have hc : ContMDiff (𝓡 1) 𝓘(ℝ, E2) ∞ (c z) := by
      have hg : ContMDiff (𝓡 1) 𝓘(ℝ, E2) ∞
          (fun q : UnitCircle => D0.chart z (q : E2)) := by
        intro p
        have hs := (G0.fiber_contDiffOn (hJband hz)).contDiffAt
          (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr
            ((norm_eq_of_mem_sphere p).trans_lt G0.one_lt_radius)))
        exact hs.contMDiffAt.comp p contMDiff_coe_sphere.contMDiffAt
      exact hg.congr (fun p => (D0.chart_boundary z (hJband hz) p).symm)
    have he : c z ∘ F z = fun q : UnitCircle => (T (z, (q : E2))).2 :=
      funext (fun q => (hF z hz q).2.2)
    have hd := mfderiv_comp q (hc.mdifferentiable (by simp) _)
      ((hFslice z hz).mdifferentiable (by simp) q)
    rw [he] at hd
    intro v w hvw
    apply (hTf.2.2 z).2.2 q
    rw [hd]
    exact congrArg (mfderiv (𝓡 1) 𝓘(ℝ, E2) (c z) (F z q)) hvw
  have hFsurj (z : ℝ) (hz : z ∈ Ioo jL jR) : Surjective (F z) := by
    let fc : ℝ → UnitCircle → E2 := fun _ q => (F z q : E2)
    have hfc : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, E2) ∞
        (fun p : ℝ × UnitCircle => fc p.1 p.2) :=
      ((contMDiff_coe_sphere (E := E2) (n := 1)).comp (hFslice z hz)).comp contMDiff_snd
    have hfi (q : UnitCircle) : Injective (mfderiv (𝓡 1) 𝓘(ℝ, E2) (fc 0) q) := by
      have hi : ContMDiff (𝓡 1) 𝓘(ℝ, E2) ∞ (fun p : UnitCircle => (p : E2)) :=
        contMDiff_coe_sphere
      change Injective (mfderiv (𝓡 1) 𝓘(ℝ, E2)
        ((fun p : UnitCircle => (p : E2)) ∘ F z) q)
      rw [mfderiv_comp q (hi.mdifferentiable (by simp) _)
        ((hFslice z hz).mdifferentiable (by simp) q)]
      apply Injective.comp _ (hFimm z hz q)
      intro v w hvw
      exact injective_mvfderiv_subtypeVal_sphere (F z q)
        (congrArg (NormedSpace.fromTangentSpace (𝕜 := ℝ) (F z q : E2)) hvw)
    let gamma : ℝ → E2 := fun t => F z (sphereCircleParameter e t)
    have hgamma : ContDiff ℝ ∞ gamma :=
      (((contMDiff_coe_sphere (E := E2) (n := 1)).comp (hFslice z hz)).comp
        (contMDiff_sphereCircleParameter e)).contDiff
    have hgn (t : ℝ) : deriv gamma t ≠ 0 :=
      deriv_curveFamily_circleParameter_ne_zero e fc hfc 0 t (hfi _)
    obtain ⟨s0, hs0⟩ := surjective_sphereCircleParameter e (F z (sphereCircleParameter e 0))
    obtain ⟨b, hb, _hb0, hbphase⟩ := exists_contDiff_sphere_parameter_lift e gamma hgamma
      (fun t => norm_eq_of_mem_sphere _) 0 s0 (congrArg Subtype.val hs0)
    have hbne (t : ℝ) : deriv b t ≠ 0 := by
      intro ht
      have hd := (hasDerivAt_sphereCircleParameter_coe e (b t)).scomp t
        (hb.differentiable (by simp) t).hasDerivAt
      have he : ((fun s => (sphereCircleParameter e s : E2)) ∘ b) = gamma := funext hbphase
      rw [he, ht, zero_smul] at hd
      exact hgn t hd.deriv
    have hbper : Periodic (fun t => sphereCircleParameter e (b t)) (2 * Real.pi) := by
      intro t
      apply Subtype.ext
      rw [hbphase, hbphase]
      exact congrArg (fun q => (F z q : E2)) (periodic_sphereCircleParameter e t)
    have hbinj (s t : ℝ) (h : sphereCircleParameter e (b s) = sphereCircleParameter e (b t)) :
        sphereCircleParameter e s = sphereCircleParameter e t := by
      apply hFinj z hz
      apply Subtype.ext
      change gamma s = gamma t
      rw [← hbphase, ← hbphase]
      exact congrArg Subtype.val h
    have hbd : Continuous (deriv b) := hb.continuous_deriv (by simp)
    have hsign : (∀ t, 0 < deriv b t) ∨ ∀ t, deriv b t < 0 := by
      rcases lt_or_gt_of_ne (hbne 0) with hneg | hpos
      · right
        intro t
        by_contra ht
        obtain ⟨r, hr⟩ := intermediate_value_univ 0 t hbd ⟨hneg.le, le_of_not_gt ht⟩
        exact hbne r hr
      · left
        intro t
        by_contra ht
        obtain ⟨r, hr⟩ := intermediate_value_univ t 0 hbd ⟨le_of_not_gt ht, hpos.le⟩
        exact hbne r hr
    have hbs : Surjective b := by
      have hp : 0 < 2 * Real.pi := by positivity
      rcases hsign with hpos | hneg
      · exact surjective_of_add_period hp hb.continuous
          (circle_lift_add_period_of_positive e b hb hpos hbper hbinj)
      · let b' : ℝ → ℝ := fun t => b (-t)
        have hb' : ContDiff ℝ ∞ b' := hb.comp contDiff_neg
        have hb'p (t : ℝ) : 0 < deriv b' t := by
          have hd := ((hb.differentiable (by simp) (-t)).hasDerivAt).comp t
            (hasDerivAt_id t).neg
          change HasDerivAt b' (deriv b (-t) * -1) t at hd
          rw [hd.deriv]
          nlinarith [hneg (-t)]
        have hb'per : Periodic (fun t => sphereCircleParameter e (b' t)) (2 * Real.pi) := by
          intro t
          change sphereCircleParameter e (b (-(t + 2 * Real.pi))) = _
          rw [neg_add, ← sub_eq_add_neg]
          exact hbper.sub_eq (-t)
        have hb'inj (s t : ℝ)
            (h : sphereCircleParameter e (b' s) = sphereCircleParameter e (b' t)) :
            sphereCircleParameter e s = sphereCircleParameter e t := by
          have hh := congrArg (fun q : UnitCircle =>
            e (starRingEnd ℂ (e.symm (q : E2)))) (hbinj (-s) (-t) h)
          apply Subtype.ext
          simpa only [sphereCircleParameter, e.symm_apply_apply, Circle.exp_neg,
            Circle.coe_inv_eq_conj, starRingEnd_self_apply] using hh
        have hs := surjective_of_add_period hp hb'.continuous
          (circle_lift_add_period_of_positive e b' hb' hb'p hb'per hb'inj)
        intro y
        obtain ⟨t, ht⟩ := hs y
        exact ⟨-t, ht⟩
    intro q
    obtain ⟨t, rfl⟩ := surjective_sphereCircleParameter e q
    obtain ⟨s, hs⟩ := hbs t
    refine ⟨sphereCircleParameter e s, Subtype.ext ?_⟩
    change gamma s = (sphereCircleParameter e t : E2)
    rw [← hbphase, hs]
  let V : ℝ → UnitCircle → UnitCircle := fun z q =>
    unitRadialProjection qbase (T.symm (G0.chart (z, (q : E2)))).2
  have hV (z : ℝ) (hz : z ∈ Ioo jL jR) (q : UnitCircle) :
      G0.chart (z, (q : E2)) ∈ T.target ∧
        (V z q : E2) = (T.symm (G0.chart (z, (q : E2)))).2 ∧
        F z (V z q) = q := by
    obtain ⟨p, rfl⟩ := hFsurj z hz q
    rw [(hF z hz p).2.1]
    have he : V z (F z p) = p := by
      change unitRadialProjection qbase (T.symm (G0.chart (z, (F z p : E2)))).2 = p
      rw [(hF z hz p).2.1, T.left_inv (hsource z p)]
      exact unitRadialProjection_apply_coe qbase p
    exact ⟨T.map_source (hsource z p), by rw [he, T.left_inv (hsource z p)], by rw [he]⟩
  have hVsm : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 1)) (𝓡 1) ∞
      (fun p : ℝ × UnitCircle => V p.1 p.2) (Ioo jL jR ×ˢ univ) := by
    apply contMDiffOn_sphere_of_coe (isOpen_Ioo.prod isOpen_univ)
    have hinner : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, P) ∞
        (fun p : ℝ × UnitCircle => G0.chart (p.1, (p.2 : E2))) (Ioo jL jR ×ˢ univ) := by
      intro p hp
      have hs := G0.smooth.contDiffAt (G0.chart.open_source.mem_nhds (hGsource p.1 hp.1 p.2))
      exact (hs.contMDiffAt.comp p (contMDiffAt_fst.prodMk_space
        (contMDiff_coe_sphere.contMDiffAt.comp p contMDiffAt_snd))).contMDiffWithinAt
    have hout := hTs.2.2.2.2.2.1.contMDiffOn.comp hinner
      (fun p hp => (hV p.1 hp.1 p.2).1)
    exact (contDiff_snd.contMDiff.comp_contMDiffOn hout).congr
      (fun p hp => (hV p.1 hp.1 p.2).2.1)
  have hVslice (z : ℝ) (hz : z ∈ Ioo jL jR) :
      ContMDiff (𝓡 1) (𝓡 1) ∞ (V z) := by
    have hp : ContMDiff (𝓡 1) (𝓘(ℝ, ℝ).prod (𝓡 1)) ∞
        (fun q : UnitCircle => (z, q)) := contMDiff_const.prodMk contMDiff_id
    exact ContMDiffOn.comp_contMDiff
      (g := fun p : ℝ × UnitCircle => V p.1 p.2) (f := fun q : UnitCircle => (z, q))
      hVsm hp (fun _ => ⟨hz, mem_univ _⟩)
  let phi : ℝ → CircleDiff := fun z => if hz : z ∈ Ioo jL jR then {
    toEquiv := {
      toFun := F z
      invFun := V z
      left_inv := fun q => hFinj z hz ((hV z hz (F z q)).2.2)
      right_inv := fun q => (hV z hz q).2.2 }
    contMDiff_toFun := hFslice z hz
    contMDiff_invFun := hVslice z hz }
    else Diffeomorph.refl (𝓡 1) UnitCircle ∞
  refine ⟨phi, ?_, ?_, ?_, ?_⟩
  · exact hFsm.congr (fun p hp => by simp only [phi, dif_pos hp.1]; rfl)
  · exact hVsm.congr (fun p hp => by simp only [phi, dif_pos hp.1]; rfl)
  · intro z hz q
    simp only [phi, dif_pos hz]
    exact ⟨(hF z hz q).1, (hV z hz q).2.1, (hF z hz q).2.2⟩
  · intro z hz q
    simp only [phi, dif_neg hz, Diffeomorph.coe_refl, id_eq]

end PoincareConjecture.M25.Topology3D
