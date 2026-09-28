import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsProfileChart
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryCapTag
import Mathlib.Analysis.Calculus.ContDiff.Deriv

set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold InnerProductSpace NNReal Topology

namespace PoincareConjecture.M25.Topology3D

variable {psi : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}

noncomputable def stackCapScale (l0 lambda t : ℝ) : ℝ :=
  (1 - Real.smoothTransition t) * l0 + Real.smoothTransition t * lambda

theorem stackCapScale_spec (l0 lambda : ℝ) (hlambda : 0 < lambda)
    (hsmall : lambda < l0) :
    ContDiff ℝ ∞ (stackCapScale l0 lambda) ∧
    ContDiff ℝ ∞ (deriv (stackCapScale l0 lambda)) ∧
    (∀ t, lambda ≤ stackCapScale l0 lambda t ∧
      stackCapScale l0 lambda t ≤ l0 ∧ 0 < stackCapScale l0 lambda t) ∧
    (∀ t, t ≤ 0 → stackCapScale l0 lambda t = l0) ∧
    (∀ t, 1 ≤ t → stackCapScale l0 lambda t = lambda) := by
  have hL : ContDiff ℝ ∞ (stackCapScale l0 lambda) :=
    ((contDiff_const.sub Real.smoothTransition.contDiff).mul contDiff_const).add
      (Real.smoothTransition.contDiff.mul contDiff_const)
  refine ⟨hL, (contDiff_infty_iff_deriv.mp hL).2, ?_, ?_, ?_⟩
  · intro t
    have hlo : lambda ≤ stackCapScale l0 lambda t := by
      have h := mul_nonneg (sub_nonneg.mpr (Real.smoothTransition.le_one t))
        (sub_nonneg.mpr hsmall.le)
      dsimp [stackCapScale]
      nlinarith
    have hhi : stackCapScale l0 lambda t ≤ l0 := by
      have h := mul_nonneg (Real.smoothTransition.nonneg t) (sub_nonneg.mpr hsmall.le)
      dsimp [stackCapScale]
      nlinarith
    exact ⟨hlo, hhi, hlambda.trans_le hlo⟩
  · intro t ht
    simp only [stackCapScale, Real.smoothTransition.zero_of_nonpos ht,
      sub_zero, one_mul, zero_mul, add_zero]
  · intro t ht
    simp only [stackCapScale, Real.smoothTransition.one_of_one_le ht,
      sub_self, zero_mul, one_mul, zero_add]

noncomputable def stackCapScalePlacementDiffeomorph
    (s l0 lambda : ℝ) (hl0 : 0 < l0) (hlambda : 0 < lambda) :
    Diffeomorph 𝓘(ℝ, ℝ × (E2 × ℝ)) 𝓘(ℝ, ℝ × (E2 × ℝ))
      (ℝ × (E2 × ℝ)) (ℝ × (E2 × ℝ)) ∞ := by
  let L := stackCapScale l0 lambda
  have hLpos (t : ℝ) : 0 < L t :=
    stackProfileBlend_pos (fun _ : Unit => l0) (fun _ : Unit => lambda) t () hl0 hlambda
  have hL : ContDiff ℝ ∞ L :=
    ((contDiff_const.sub Real.smoothTransition.contDiff).mul contDiff_const).add
      (Real.smoothTransition.contDiff.mul contDiff_const)
  refine {
    toEquiv := {
      toFun := fun p => (p.1, p.2.1, s + (L p.1 / l0) * (p.2.2 - s))
      invFun := fun p => (p.1, p.2.1, s + (l0 / L p.1) * (p.2.2 - s))
      left_inv := ?_
      right_inv := ?_ }
    contMDiff_toFun := ?_
    contMDiff_invFun := ?_ }
  · rintro ⟨t, x, z⟩
    change (t, x, s + l0 / L t * (s + L t / l0 * (z - s) - s)) = (t, x, z)
    congr 2
    field_simp [hl0.ne', (hLpos t).ne']
    ring
  · rintro ⟨t, x, z⟩
    change (t, x, s + L t / l0 * (s + l0 / L t * (z - s) - s)) = (t, x, z)
    congr 2
    field_simp [hl0.ne', (hLpos t).ne']
    ring
  · exact (contDiff_fst.prodMk (contDiff_snd.fst.prodMk
      (contDiff_const.add (((hL.comp contDiff_fst).div_const l0).mul
        (contDiff_snd.snd.sub contDiff_const))))).contMDiff
  · exact (contDiff_fst.prodMk (contDiff_snd.fst.prodMk
      (contDiff_const.add ((contDiff_const.div (hL.comp contDiff_fst)
        (fun p => (hLpos p.1).ne')).mul
          (contDiff_snd.snd.sub contDiff_const))))).contMDiff

theorem stackCapScalePlacementDiffeomorph_spec
    (s l0 lambda : ℝ) (hl0 : 0 < l0) (hlambda : 0 < lambda) :
    let D := stackCapScalePlacementDiffeomorph s l0 lambda hl0 hlambda
    (∀ t x z, D (t, x, z) =
      (t, x, s + (stackCapScale l0 lambda t / l0) * (z - s))) ∧
    (∀ t x z, D.symm (t, x, z) =
      (t, x, s + (l0 / stackCapScale l0 lambda t) * (z - s))) := by
  exact ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩

noncomputable def stackCapScaleChart (C : SurgeryCapTag psi u)
    (lambda : ℝ) (hlambda : 0 < lambda) :
    OpenPartialHomeomorph (ℝ × E3) (ℝ × E3) :=
  let s := C.cutHeight + C.sign * C.removal
  let D := stackCapScalePlacementDiffeomorph s C.scale lambda C.scale_pos hlambda
  (((Homeomorph.refl ℝ).prodCongr heightCoordinates.toHomeomorph).trans
    D.toHomeomorph).toOpenPartialHomeomorph.trans
      ((OpenPartialHomeomorph.refl ℝ).prod C.tube)

theorem stackCapScaleChart_spec (C : SurgeryCapTag psi u)
    (lambda : ℝ) (hlambda : 0 < lambda) :
    let s := C.cutHeight + C.sign * C.removal
    let a := fun t => stackCapScale C.scale lambda t / C.scale
    let e := stackCapScaleChart C lambda hlambda
    (∀ t x, e (t, x) = (t, C.tube ((heightCoordinates x).1,
      s + a t * ((heightCoordinates x).2 - s)))) ∧
    (∀ t y, e.symm (t, y) = (t, heightCoordinates.symm
      ((C.tube.symm y).1, s + (a t)⁻¹ * ((C.tube.symm y).2 - s)))) ∧
    e.source = {p | ((heightCoordinates p.2).1,
      s + a p.1 * ((heightCoordinates p.2).2 - s)) ∈ C.tube.source} ∧
    e.target = univ ×ˢ C.tube.target ∧
    ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
    ∀ p, (e p).1 = p.1 := by
  let s := C.cutHeight + C.sign * C.removal
  let a := fun t => stackCapScale C.scale lambda t / C.scale
  let e := stackCapScaleChart C lambda hlambda
  let D := stackCapScalePlacementDiffeomorph s C.scale lambda C.scale_pos hlambda
  have hforward (t : ℝ) (x : E3) : e (t, x) =
      (t, C.tube ((heightCoordinates x).1, s + a t * ((heightCoordinates x).2 - s))) := rfl
  have hinverse (t : ℝ) (y : E3) : e.symm (t, y) =
      (t, heightCoordinates.symm ((C.tube.symm y).1,
        s + (a t)⁻¹ * ((C.tube.symm y).2 - s))) := by
    change (t, heightCoordinates.symm ((C.tube.symm y).1,
      s + (C.scale / stackCapScale C.scale lambda t) * ((C.tube.symm y).2 - s))) = _
    simp only [a, inv_div]
  have hsource : e.source = {p | ((heightCoordinates p.2).1,
      s + a p.1 * ((heightCoordinates p.2).2 - s)) ∈ C.tube.source} := by
    ext p
    change (True ∧ (True ∧ ((heightCoordinates p.2).1,
      s + a p.1 * ((heightCoordinates p.2).2 - s)) ∈ C.tube.source)) ↔ _
    simp only [true_and, mem_ofPred_eq]
  have htarget : e.target = univ ×ˢ C.tube.target := by
    ext p
    change ((True ∧ p.2 ∈ C.tube.target) ∧ True) ↔ (True ∧ p.2 ∈ C.tube.target)
    simp only [and_true]
  have hD : ContDiff ℝ ∞ (fun p : ℝ × E3 =>
      D (p.1, heightCoordinates p.2)) :=
    D.contMDiff_toFun.contDiff.comp
      (contDiff_fst.prodMk (heightCoordinates.contDiff.comp contDiff_snd))
  have hT : ContDiffOn ℝ ∞ (fun p : ℝ × E3 =>
      C.tube (D (p.1, heightCoordinates p.2)).2) e.source :=
    C.tube_smooth.comp hD.snd.contDiffOn (fun p hp => by
      change ((heightCoordinates p.2).1,
        s + a p.1 * ((heightCoordinates p.2).2 - s)) ∈ C.tube.source
      rw [hsource] at hp
      exact hp)
  have hTi : ContDiffOn ℝ ∞ (fun p : ℝ × E3 => C.tube.symm p.2) e.target :=
    C.tube_inverse.comp contDiff_snd.contDiffOn (fun p hp => (htarget ▸ hp).2)
  have hDi : ContDiffOn ℝ ∞ (fun p : ℝ × E3 => D.symm (p.1, C.tube.symm p.2)) e.target :=
    D.symm.contMDiff_toFun.contDiff.comp_contDiffOn (contDiff_fst.contDiffOn.prodMk hTi)
  exact ⟨hforward, hinverse, hsource, htarget, contDiff_fst.contDiffOn.prodMk hT,
    contDiff_fst.contDiffOn.prodMk
      (heightCoordinates.symm.contDiff.comp_contDiffOn hDi.snd), fun _ => rfl⟩

noncomputable def stackCapScaleCap (C : SurgeryCapTag psi u)
    (lambda t : ℝ) (q : UnitTwoSphere) : E3 :=
  C.profile.capMap C.tube C.cutHeight C.sign C.removal
    (stackCapScale C.scale lambda t) q

theorem stackCapScaleCap_spec (C : SurgeryCapTag psi u)
    (lambda : ℝ) (hlambda : 0 < lambda) (hsmall : lambda < C.scale) :
    let e := stackCapScaleChart C lambda hlambda
    let cap := stackCapScaleCap C lambda
    let Ktrack := (fun p : ℝ × UnitTwoSphere => (p.1, cap p.1 p.2)) ''
      (Icc (-1 : ℝ) 2 ×ˢ {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0})
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) ∞
      (fun p : ℝ × UnitTwoSphere => cap p.1 p.2) ∧
    (∀ t q, ((C.profile.model q).1, C.cutHeight + C.sign *
      (C.removal + stackCapScale C.scale lambda t * (C.profile.model q).2))
        ∈ C.tube.source) ∧
    (∀ t q, HasDerivAt (fun z => cap z q)
      (chartTimeField e (t, cap t q)) t) ∧
    IsCompact Ktrack ∧ Ktrack ⊆ e.target ∧
    (∀ q, cap 0 q = C.profile.capMap C.tube C.cutHeight C.sign C.removal C.scale q) ∧
    (∀ q, cap 1 q = C.profile.capMap C.tube C.cutHeight C.sign C.removal lambda q) ∧
    (∀ t q, C.sign * (inner ℝ (u : E3) (cap t q) -
      (C.cutHeight + C.sign * C.removal)) =
        stackCapScale C.scale lambda t * (C.profile.model q).2) ∧
    (∀ t q, |inner ℝ (u : E3) (cap t q) -
      (C.cutHeight + C.sign * C.removal)| ≤ C.scale * C.profile.heightBound) ∧
    (∀ (t : ℝ) (q : UnitTwoSphere), (heightCoordinates (q : E3)).2 ≤ 0 →
      C.sign * (inner ℝ (u : E3) (cap t q) -
        (C.cutHeight + C.sign * C.removal)) ≤ 0) ∧
    (∀ (t : ℝ) (q : UnitTwoSphere), (heightCoordinates (q : E3)).2 ≤ 0 →
      (C.sign * (inner ℝ (u : E3) (cap t q) -
        (C.cutHeight + C.sign * C.removal)) = 0 ↔
          (heightCoordinates (q : E3)).2 = 0)) ∧
    ∀ (t : ℝ) (q : UnitTwoSphere), (heightCoordinates (q : E3)).2 = 0 →
      cap t q = cap 0 q := by
  let e := stackCapScaleChart C lambda hlambda
  let cap := stackCapScaleCap C lambda
  obtain ⟨hL, _, hbounds, hstart, hfinish⟩ :=
    stackCapScale_spec C.scale lambda hlambda hsmall
  obtain ⟨hforward, _, hsource, htarget, he, _, htime⟩ :=
    stackCapScaleChart_spec C lambda hlambda
  have hs (t : ℝ) (q : UnitTwoSphere) :
      ((C.profile.model q).1, C.cutHeight + C.sign *
        (C.removal + stackCapScale C.scale lambda t * (C.profile.model q).2))
          ∈ C.tube.source :=
    C.tube_source ⟨mem_closedBall_zero_iff.mpr (C.profile.model_fst_norm_le q), mem_univ _⟩
  have hM : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E2 × ℝ) ∞
      (fun p : ℝ × UnitTwoSphere => C.profile.model p.2) :=
    C.profile.model_contMDiff.comp contMDiff_snd
  have hLt : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × UnitTwoSphere => stackCapScale C.scale lambda p.1) :=
    hL.comp_contMDiff contMDiff_fst
  have hcoords : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E2 × ℝ) ∞
      (fun p : ℝ × UnitTwoSphere => ((C.profile.model p.2).1,
        C.cutHeight + C.sign * (C.removal + stackCapScale C.scale lambda p.1 *
          (C.profile.model p.2).2))) :=
    (contDiff_fst.comp_contMDiff hM).prodMk_space
    (contMDiff_const.add (contMDiff_const.mul
      (contMDiff_const.add (hLt.mul (contDiff_snd.comp_contMDiff hM)))))
  have hcap : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) ∞
      (fun p : ℝ × UnitTwoSphere => cap p.1 p.2) := by
    apply contMDiffOn_univ.mp
    exact C.tube_smooth.contMDiffOn.comp hcoords.contMDiffOn (fun p _ => hs p.1 p.2)
  have htrack (t : ℝ) (q : UnitTwoSphere) :
      HasDerivAt (fun z => cap z q) (chartTimeField e (t, cap t q)) t := by
    let X := heightCoordinates.symm ((C.profile.model q).1,
      C.cutHeight + C.sign * (C.removal + C.scale * (C.profile.model q).2))
    have hc (r : ℝ) :
        C.cutHeight + C.sign * C.removal + stackCapScale C.scale lambda r / C.scale *
          ((heightCoordinates X).2 - (C.cutHeight + C.sign * C.removal)) =
        C.cutHeight + C.sign * (C.removal + stackCapScale C.scale lambda r *
          (C.profile.model q).2) := by
      dsimp only [X]
      rw [heightCoordinates.apply_symm_apply]
      field_simp [C.scale_pos.ne']
      ring
    have hX : (t, X) ∈ e.source := by
      rw [hsource]
      dsimp only [mem_ofPred_eq]
      rw [hc]
      simpa only [X, heightCoordinates.apply_symm_apply] using hs t q
    have hformula (r : ℝ) : (e (r, X)).2 = cap r q := by
      rw [hforward]
      change C.tube ((heightCoordinates X).1, _) = _
      rw [hc]
      simp only [X, heightCoordinates.apply_symm_apply]
      rfl
    simpa only [hformula] using chartTimeField_track e he
      (fun p _ => htime p) t X hX
  have hheight (t : ℝ) (q : UnitTwoSphere) :
      C.sign * (inner ℝ (u : E3) (cap t q) -
        (C.cutHeight + C.sign * C.removal)) =
          stackCapScale C.scale lambda t * (C.profile.model q).2 := by
    have hsign : C.sign * C.sign = 1 := by nlinarith [C.sign_abs, sq_abs C.sign]
    change C.sign * (inner ℝ (u : E3) (C.tube ((C.profile.model q).1,
      C.cutHeight + C.sign * (C.removal + stackCapScale C.scale lambda t *
        (C.profile.model q).2))) - _) = _
    rw [C.tube_height _ (hs t q)]
    calc
      _ = (C.sign * C.sign) *
          (stackCapScale C.scale lambda t * (C.profile.model q).2) := by ring
      _ = _ := by rw [hsign, one_mul]
  have hmodelzero (q : UnitTwoSphere) : (C.profile.model q).2 = 0 ↔
      (heightCoordinates (q : E3)).2 = 0 := by
    change C.profile.vertical (C.profile.horizontal (heightCoordinates (q : E3)).2 •
      (heightCoordinates (q : E3)).1) * (heightCoordinates (q : E3)).2 = 0 ↔ _
    simp only [mul_eq_zero, (C.profile.vertical_pos _).ne', false_or]
  have hheightContinuous : Continuous (fun q : UnitTwoSphere =>
      (heightCoordinates (q : E3)).2) :=
    (heightCoordinates.continuous.comp continuous_subtype_val).snd
  refine ⟨hcap, hs, htrack,
    (isCompact_Icc.prod (isClosed_le hheightContinuous continuous_const).isCompact).image
      (continuous_fst.prodMk hcap.continuous), ?_, ?_, ?_, hheight, ?_, ?_, ?_, ?_⟩
  · rintro p ⟨⟨t, q⟩, _, rfl⟩
    rw [htarget]
    exact ⟨mem_univ _, C.tube.map_source (hs t q)⟩
  · intro q
    change C.profile.capMap _ _ _ _ (stackCapScale C.scale lambda 0) q = _
    rw [hstart 0 le_rfl]
  · intro q
    change C.profile.capMap _ _ _ _ (stackCapScale C.scale lambda 1) q = _
    rw [hfinish 1 le_rfl]
  · intro t q
    have habs : |inner ℝ (u : E3) (cap t q) -
        (C.cutHeight + C.sign * C.removal)| =
        |stackCapScale C.scale lambda t * (C.profile.model q).2| := by
      rw [← hheight, abs_mul, C.sign_abs, one_mul]
    rw [habs, abs_mul, abs_of_pos (hbounds t).2.2]
    exact mul_le_mul (hbounds t).2.1 (C.profile.height_bound q)
      (abs_nonneg _) C.scale_pos.le
  · intro t q hq
    rw [hheight]
    apply mul_nonpos_of_nonneg_of_nonpos (hbounds t).2.2.le
    exact (surgeryCapModel_snd_nonpos_iff _ _ _ _ _ _ C.profile.vertical_pos q).mpr hq
  · intro t q _
    rw [hheight, mul_eq_zero]
    simp only [(hbounds t).2.2.ne', false_or, hmodelzero]
  · intro t q hq
    have hz := (hmodelzero q).mpr hq
    change C.tube ((C.profile.model q).1,
      C.cutHeight + C.sign * (C.removal + stackCapScale C.scale lambda t *
        (C.profile.model q).2)) = C.tube ((C.profile.model q).1,
      C.cutHeight + C.sign * (C.removal + stackCapScale C.scale lambda 0 *
        (C.profile.model q).2))
    rw [hz]
    simp only [mul_zero]

theorem stackCapScaleChart_field_tube (C : SurgeryCapTag psi u)
    (lambda : ℝ) (hlambda : 0 < lambda) (t : ℝ) (x : E2) (z : ℝ)
    (hxz : (x, z) ∈ C.tube.source) :
    chartTimeField (stackCapScaleChart C lambda hlambda) (t, C.tube (x, z)) =
      ((deriv (stackCapScale C.scale lambda) t /
          stackCapScale C.scale lambda t) *
        (z - (C.cutHeight + C.sign * C.removal))) •
          (fderiv ℝ C.tube (x, z) (0, 1)) := by
  let L := stackCapScale C.scale lambda
  let s := C.cutHeight + C.sign * C.removal
  let v := s + (C.scale / L t) * (z - s)
  let X := heightCoordinates.symm (x, v)
  let e := stackCapScaleChart C lambda hlambda
  have hLpos : 0 < L t :=
    stackProfileBlend_pos (fun _ : Unit => C.scale) (fun _ : Unit => lambda)
      t () C.scale_pos hlambda
  have hL : ContDiff ℝ ∞ L :=
    ((contDiff_const.sub Real.smoothTransition.contDiff).mul contDiff_const).add
      (Real.smoothTransition.contDiff.mul contDiff_const)
  obtain ⟨hforward, _, hsource, _, he, _, htime⟩ := stackCapScaleChart_spec C lambda hlambda
  have hzt : s + L t / C.scale * (v - s) = z := by
    dsimp only [v]
    field_simp [C.scale_pos.ne', hLpos.ne']
    ring
  have hX : (t, X) ∈ e.source := by
    rw [hsource]
    change ((heightCoordinates X).1, s + L t / C.scale * ((heightCoordinates X).2 - s))
      ∈ C.tube.source
    dsimp only [X]
    rw [heightCoordinates.apply_symm_apply, hzt]
    exact hxz
  have hformula (r : ℝ) : (e (r, X)).2 =
      C.tube (x, s + L r / C.scale * (v - s)) := by
    rw [hforward]
    simp only [X, heightCoordinates.apply_symm_apply]
    rfl
  have htrack : HasDerivAt (fun r => C.tube (x, s + L r / C.scale * (v - s)))
      (chartTimeField e (t, C.tube (x, z))) t := by
    simpa only [hformula, hzt] using chartTimeField_track e he
      (fun p _ => htime p) t X hX
  have harg : HasDerivAt (fun r => (x, s + L r / C.scale * (v - s)))
      (0, deriv L t / C.scale * (v - s)) t :=
    (hasDerivAt_const t x).prodMk
      ((((hL.differentiable (by simp) t).hasDerivAt.div_const C.scale).mul_const
        (v - s)).const_add s)
  have hT := (C.tube_smooth.contDiffAt (C.tube.open_source.mem_nhds hxz)).differentiableAt
    (by simp)
  have hT' : HasFDerivAt C.tube (fderiv ℝ C.tube (x, z))
      (x, s + L t / C.scale * (v - s)) := by
    rw [hzt]
    exact hT.hasFDerivAt
  have hderiv := hT'.comp_hasDerivAt t harg
  have hcoef : deriv L t / C.scale * (v - s) = deriv L t / L t * (z - s) := by
    dsimp only [v]
    field_simp [C.scale_pos.ne', hLpos.ne']
    ring
  have hvector : (0, deriv L t / C.scale * (v - s)) =
      (deriv L t / L t * (z - s)) • ((0 : E2), (1 : ℝ)) := by
    rw [hcoef]
    simp only [Prod.smul_mk, smul_zero, smul_eq_mul, mul_one]
  rw [hvector, map_smul] at hderiv
  exact htrack.unique hderiv

end PoincareConjecture.M25.Topology3D
