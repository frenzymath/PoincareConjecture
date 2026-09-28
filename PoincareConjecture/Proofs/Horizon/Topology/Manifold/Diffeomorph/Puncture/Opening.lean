import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.InverseFunction.ModelSpaces
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.EssentialSphere.RadialCylinder
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace Filter
open scoped Manifold ContDiff Topology

namespace Poincare


def positiveHalfLine : Opens ℝ := ⟨Ioi 0, isOpen_Ioi⟩

private def openingInverse (δ : ℝ) (s : ℝ) : ℝ :=
  s - (1 - Real.smoothTransition (2 * s / δ - 1)) / s

private theorem openingInverse_fixed {δ : ℝ} (hδ : 0 < δ)
    {s : ℝ} (hs : δ ≤ s) : openingInverse δ s = s := by
  have harg : 1 ≤ 2 * s / δ - 1 := by
    have : 2 ≤ 2 * s / δ := (le_div_iff₀ hδ).mpr (by linarith)
    linarith
  simp [openingInverse, Real.smoothTransition.one_of_one_le harg]

private theorem openingInverse_small {δ : ℝ} (hδ : 0 < δ)
    {s : ℝ} (hs : s ≤ δ / 2) : openingInverse δ s = s - s⁻¹ := by
  have harg : 2 * s / δ - 1 ≤ 0 := by
    have : 2 * s / δ ≤ 1 := (div_le_iff₀ hδ).mpr (by linarith)
    linarith
  simp [openingInverse, Real.smoothTransition.zero_of_nonpos harg]

private theorem openingInverse_contDiffOn (δ : ℝ) :
    ContDiffOn ℝ ∞ (openingInverse δ) (Ioi 0) := by
  apply contDiff_id.contDiffOn.sub
  apply ContDiffOn.div
  · exact (contDiff_const.sub (Real.smoothTransition.contDiff.comp
      (((contDiff_const.mul contDiff_id).div_const δ).sub contDiff_const))).contDiffOn
  · exact contDiff_id.contDiffOn
  · intro s hs
    exact ne_of_gt hs

private theorem openingInverse_hasDerivAt {δ : ℝ} (hδ : 0 < δ)
    {s : ℝ} (hs : 0 < s) :
    ∃ a : ℝ, 0 < a ∧ HasDerivAt (openingInverse δ) a s := by
  let z := 2 * s / δ - 1
  let a := 1 + ((deriv Real.smoothTransition z * (2 / δ)) * s +
    (1 - Real.smoothTransition z)) / s ^ 2
  have hstep := ((Real.smoothTransition.contDiff :
    ContDiff ℝ ∞ Real.smoothTransition).differentiable (by simp) z).hasDerivAt
  have hd : HasDerivAt (fun x : ℝ => Real.smoothTransition (2 * x / δ - 1))
      (deriv Real.smoothTransition z * (2 / δ)) s := by
    convert hstep.comp s ((((hasDerivAt_id s).const_mul 2).div_const δ).sub_const 1)
      using 1 <;> first | rfl | ring
  have hderiv := (hasDerivAt_id s).sub
    (((hasDerivAt_const s (1 : ℝ)).sub hd).div (hasDerivAt_id s) hs.ne')
  refine ⟨a, ?_, ?_⟩
  · have hnonneg := Real.smoothTransition.monotone.deriv_nonneg (x := z)
    have hle := Real.smoothTransition.le_one z
    dsimp [a]
    positivity
  · convert hderiv using 1 <;> first | rfl | (dsimp [a, z]; ring)

private theorem openingInverse_strictMonoOn {δ : ℝ} (hδ : 0 < δ) :
    StrictMonoOn (openingInverse δ) (Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0) (openingInverse_contDiffOn δ).continuousOn
  intro s hs
  have hs' : 0 < s := by simpa only [interior_Ioi, mem_Ioi] using hs
  obtain ⟨a, ha, hd⟩ := openingInverse_hasDerivAt hδ hs'
  rwa [hd.deriv]

private theorem openingInverse_surjOn {δ : ℝ} (hδ : 0 < δ) :
    SurjOn (openingInverse δ) (Ioi 0) univ := by
  intro y _
  let a := min (δ / 2) (1 / (|y| + 2))
  let b := max δ (y + 1)
  have hden : 0 < |y| + 2 := by positivity
  have ha : 0 < a := lt_min (by positivity) (one_div_pos.mpr hden)
  have haδ : a ≤ δ / 2 := min_le_left _ _
  have hab : a ≤ b := (haδ.trans (by linarith)).trans (le_max_left _ _)
  have ha1 : a ≤ 1 := (min_le_right _ _).trans
    ((div_le_one hden).mpr (by linarith [abs_nonneg y]))
  have hainv : |y| + 2 ≤ a⁻¹ := by
    apply (le_inv_comm₀ hden ha).mpr
    simpa only [a, one_div] using (min_le_right (δ / 2) (1 / (|y| + 2)))
  have hleft : openingInverse δ a ≤ y := by
    rw [openingInverse_small hδ haδ]
    linarith [neg_abs_le y]
  have hright : y ≤ openingInverse δ b := by
    rw [openingInverse_fixed hδ (le_max_left _ _)]
    linarith [le_max_right δ (y + 1)]
  obtain ⟨s, hs, hsy⟩ := intermediate_value_Icc hab
    ((openingInverse_contDiffOn δ).continuousOn.mono (fun s hs => ha.trans_le hs.1))
      ⟨hleft, hright⟩
  exact ⟨s, ha.trans_le hs.1, hsy⟩



theorem exists_halfLine_opening {δ : ℝ} (hδ : 0 < δ) :
    ∃ F : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ positiveHalfLine ∞,
      StrictMono (fun t : ℝ => (F t : ℝ)) ∧
      (∀ t : ℝ, δ ≤ t → (F t : ℝ) = t) ∧
      ∀ s : positiveHalfLine, F.symm s =
        (s : ℝ) - (1 - Real.smoothTransition (2 * (s : ℝ) / δ - 1)) / (s : ℝ) := by
  let h : ℝ → ℝ := fun t => openingInverse δ (Real.exp t)
  have hkmono := openingInverse_strictMonoOn hδ
  have hhmono : StrictMono h := fun s t hst =>
    hkmono (Real.exp_pos s) (Real.exp_pos t) (Real.exp_lt_exp.mpr hst)
  have hhsurj : Function.Surjective h := by
    intro y
    obtain ⟨s, hs, hsy⟩ := openingInverse_surjOn hδ (mem_univ y)
    exact ⟨Real.log s, by simpa only [h, Real.exp_log hs] using hsy⟩
  have hh : ContDiff ℝ ∞ h := by
    rw [← contDiffOn_univ]
    exact (openingInverse_contDiffOn δ).comp Real.contDiff_exp.contDiffOn
      (fun t _ => Real.exp_pos t)
  let e := Equiv.ofBijective h ⟨hhmono.injective, hhsurj⟩
  have hei : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ e.symm := by
    intro y
    obtain ⟨t, rfl⟩ := e.surjective y
    obtain ⟨a, ha, hd⟩ := openingInverse_hasDerivAt hδ (Real.exp_pos t)
    have hd' : HasDerivAt h (a * Real.exp t) t := hd.comp t (Real.hasDerivAt_exp t)
    apply Poincare.Geometry.Manifold.contMDiffAt_of_local_left_inverse_modelSpaces
      hh.contMDiff.contMDiffAt ?_ (Eventually.of_forall e.symm_apply_apply)
    rw [mfderiv_eq_fderiv]
    change Function.Bijective (fun z : ℝ => fderiv ℝ h t z)
    simp only [fderiv_eq_deriv_mul, hd'.deriv]
    have hn : a * Real.exp t ≠ 0 := (mul_pos ha (Real.exp_pos t)).ne'
    refine ⟨fun x y hxy => mul_left_cancel₀ hn hxy, fun y => ⟨y / (a * Real.exp t), ?_⟩⟩
    field_simp
  let f : ℝ → positiveHalfLine := fun t => ⟨Real.exp (e.symm t), Real.exp_pos _⟩
  let g : positiveHalfLine → ℝ := fun s => openingInverse δ s
  have hleft : Function.LeftInverse g f := e.apply_symm_apply
  have hright : Function.RightInverse g f := by
    intro s
    apply Subtype.ext
    change Real.exp (e.symm (openingInverse δ s)) = (s : ℝ)
    have hs : 0 < (s : ℝ) := s.property
    have hlog : openingInverse δ s = e (Real.log s) := by
      change openingInverse δ s = openingInverse δ (Real.exp (Real.log s))
      rw [Real.exp_log hs]
    rw [hlog, e.symm_apply_apply, Real.exp_log hs]
  have hf : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ f := by
    apply (ContMDiff.subtypeVal_comp_iff positiveHalfLine f).mp
    exact Real.contDiff_exp.contMDiff.comp hei
  have hg : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ g := by
    intro s
    exact ((openingInverse_contDiffOn δ).contDiffAt
      (isOpen_Ioi.mem_nhds s.property)).contMDiffAt.comp s contMDiff_subtype_val.contMDiffAt
  let F : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ positiveHalfLine ∞ :=
    ⟨⟨f, g, hleft, hright⟩, hf, hg⟩
  refine ⟨F, ?_, ?_, fun _ => rfl⟩
  · intro s t hst
    apply hkmono.lt_iff_lt (show 0 < (F s : ℝ) from (F s).property)
      (show 0 < (F t : ℝ) from (F t).property) |>.mp
    exact (show openingInverse δ (F s) < openingInverse δ (F t) by
      simpa only [← show ∀ x, F.symm x = openingInverse δ x from fun _ => rfl,
        F.symm_apply_apply] using hst)
  · intro t ht
    have htpos := hδ.trans_le ht
    have hs : F.symm ⟨t, htpos⟩ = t := openingInverse_fixed hδ ht
    have heq := congrArg F hs
    simpa only [F.apply_symm_apply] using (congrArg Subtype.val heq).symm

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S2" => Metric.sphere (0 : E3) 1
local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)


def unitBallExterior : Opens E3 :=
  ⟨{x | 1 < ‖x‖}, isOpen_lt continuous_const continuous_norm⟩



theorem exists_cylinder_diffeomorph_exterior
    (F : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ positiveHalfLine ∞) :
    ∃ G : Diffeomorph CylModel (𝓡 3) (S2 × ℝ) unitBallExterior ∞,
      ∀ p : S2 × ℝ, (G p : E3) = Real.exp (F p.2 : ℝ) • (p.1 : E3) := by
  let : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
  let f : S2 × ℝ → unitBallExterior := fun p =>
    ⟨Real.exp (F p.2 : ℝ) • (p.1 : E3), by
      change 1 < ‖Real.exp (F p.2 : ℝ) • (p.1 : E3)‖
      simpa [norm_smul, Real.norm_eq_abs, Real.abs_exp] using
        Real.one_lt_exp_iff.mpr (F p.2).property⟩
  have hxpos (x : unitBallExterior) : 0 < ‖(x : E3)‖ := lt_trans zero_lt_one x.property
  let g : unitBallExterior → S2 × ℝ := fun x =>
    (⟨‖(x : E3)‖⁻¹ • (x : E3), by
      simp [norm_smul, (hxpos x).ne']⟩,
      F.symm ⟨Real.log ‖(x : E3)‖, Real.log_pos x.property⟩)
  have hleft : Function.LeftInverse g f := by
    rintro ⟨q, t⟩
    apply Prod.ext
    · apply Subtype.ext
      simp [g, f, norm_smul, Real.norm_eq_abs, Real.abs_exp, smul_smul]
    · change F.symm ⟨Real.log ‖Real.exp (F t : ℝ) • (q : E3)‖, _⟩ = t
      have hn : ‖Real.exp (F t : ℝ) • (q : E3)‖ = Real.exp (F t : ℝ) := by
        simp [norm_smul, Real.norm_eq_abs, Real.abs_exp]
      have hp : 0 < Real.log ‖Real.exp (F t : ℝ) • (q : E3)‖ := by
        rw [hn, Real.log_exp]
        exact (F t).property
      have heq : (⟨Real.log ‖Real.exp (F t : ℝ) • (q : E3)‖, hp⟩ : positiveHalfLine) = F t := by
        apply Subtype.ext
        change Real.log ‖Real.exp (F t : ℝ) • (q : E3)‖ = (F t : ℝ)
        rw [hn, Real.log_exp]
      rw [heq, F.symm_apply_apply]
  have hright : Function.RightInverse g f := by
    intro x
    apply Subtype.ext
    change Real.exp (F (F.symm ⟨Real.log ‖(x : E3)‖, _⟩) : ℝ) •
      (‖(x : E3)‖⁻¹ • (x : E3)) = (x : E3)
    rw [F.apply_symm_apply]
    simp [Real.exp_log (hxpos x), smul_smul, (hxpos x).ne']
  have hf : ContMDiff CylModel (𝓡 3) ∞ f := by
    apply (ContMDiff.subtypeVal_comp_iff unitBallExterior f).mp
    exact (Real.contDiff_exp.contMDiff.comp
      (contMDiff_subtype_val.comp (F.contMDiff.comp contMDiff_snd))).smul
      (contMDiff_coe_sphere.comp contMDiff_fst)
  have hv : ContMDiff (𝓡 3) (𝓡 3) ∞ (fun x : unitBallExterior => (x : E3)) :=
    contMDiff_subtype_val
  have hn : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (fun x : unitBallExterior => ‖(x : E3)‖) := by
    intro x
    exact ((contDiffAt_norm ℝ (norm_pos_iff.mp (hxpos x))).contMDiffAt).comp
      x hv.contMDiffAt
  have hlog : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞
      (fun x : unitBallExterior => Real.log ‖(x : E3)‖) := by
    intro x
    exact (Real.contDiffAt_log.mpr (hxpos x).ne').contMDiffAt.comp x hn.contMDiffAt
  have hg : ContMDiff (𝓡 3) CylModel ∞ g := by
    apply ContMDiff.prodMk
    · apply ContMDiff.codRestrict_sphere
      exact (hn.inv₀ (fun x => (hxpos x).ne')).smul hv
    · apply F.symm.contMDiff.comp
      apply (ContMDiff.subtypeVal_comp_iff positiveHalfLine _).mp
      exact hlog
  exact ⟨⟨⟨f, g, hleft, hright⟩, hf, hg⟩, fun _ => rfl⟩



theorem exists_puncture_ball_opening {δ : ℝ} (hδ : 0 < δ) :
    ∃ (F : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ positiveHalfLine ∞)
      (D : Diffeomorph (𝓡 3) (𝓡 3) puncturedThreeSpace unitBallExterior ∞),
      StrictMono (fun t : ℝ => (F t : ℝ)) ∧
      (∀ t : ℝ, δ ≤ t → (F t : ℝ) = t) ∧
      (∀ p : S2 × ℝ, (D (sphereCylinderDiffeomorphPunctured p) : E3) =
        Real.exp (F p.2 : ℝ) • (p.1 : E3)) ∧
      ∀ x : puncturedThreeSpace, Real.exp δ ≤ ‖(x : E3)‖ → (D x : E3) = x := by
  obtain ⟨F, hFmono, hFfix, _⟩ := exists_halfLine_opening hδ
  obtain ⟨G, hG⟩ := exists_cylinder_diffeomorph_exterior F
  let D := sphereCylinderDiffeomorphPunctured.symm.trans G
  have hD (p : S2 × ℝ) : (D (sphereCylinderDiffeomorphPunctured p) : E3) =
      Real.exp (F p.2 : ℝ) • (p.1 : E3) := by
    change (G (sphereCylinderDiffeomorphPunctured.symm
      (sphereCylinderDiffeomorphPunctured p)) : E3) = _
    rw [Diffeomorph.symm_apply_apply, hG]
  refine ⟨F, D, hFmono, hFfix, hD, ?_⟩
  intro x hx
  obtain ⟨p, rfl⟩ := sphereCylinderDiffeomorphPunctured.surjective x
  have ht : δ ≤ p.2 := by
    apply Real.exp_le_exp.mp
    simpa [sphereCylinderDiffeomorphPunctured_apply, norm_smul,
      Real.norm_eq_abs, Real.abs_exp] using hx
  change (D (sphereCylinderDiffeomorphPunctured p) : E3) =
    (sphereCylinderDiffeomorphPunctured p : E3)
  rw [hD, hFfix _ ht, sphereCylinderDiffeomorphPunctured_apply]

end Poincare
