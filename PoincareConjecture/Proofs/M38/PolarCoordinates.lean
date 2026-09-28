import PoincareConjecture.Proofs.M38.RadialCoordinates
import Mathlib.Topology.MetricSpace.Thickening









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M38


noncomputable def capUnitDirection (x : StandardCapSpace) : UnitTwoSphere := by
  classical
  exact if hx : x = 0 then
    ⟨EuclideanSpace.single (0 : Fin 3) (1 : ℝ), by simp⟩
  else
    ⟨‖x‖⁻¹ • x, by
      simp [norm_smul, norm_ne_zero_iff.mpr hx]⟩


theorem capUnitDirection_coe {x : StandardCapSpace} (hx : x ≠ 0) :
    (capUnitDirection x).val = ‖x‖⁻¹ • x := by
  simp [capUnitDirection, hx]


theorem capUnitDirection_radial (x : StandardCapSpace) :
    ‖x‖ • (capUnitDirection x).val = x := by
  by_cases hx : x = 0
  · simp [hx]
  rw [capUnitDirection_coe hx, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]


theorem capUnitDirection_smul (z : UnitTwoSphere) {t : ℝ} (ht : 0 < t) :
    capUnitDirection (t • z.val) = z := by
  have hz : ‖z.val‖ = 1 := by simp
  have hzn : z.val ≠ 0 := by
    intro h
    simpa [h] using hz
  apply Subtype.ext
  rw [capUnitDirection_coe (smul_ne_zero ht.ne' hzn), norm_smul,
    Real.norm_eq_abs, abs_of_pos ht, hz, mul_one, smul_smul,
    inv_mul_cancel₀ ht.ne', one_smul]



theorem capUnitDirection_smooth :
    ContMDiffOn (𝓡 3) (𝓡 2) ∞ capUnitDirection ({0}ᶜ : Set StandardCapSpace) := by
  let U : TopologicalSpace.Opens StandardCapSpace := ⟨{0}ᶜ, isOpen_compl_singleton⟩
  let : Fact (Module.finrank ℝ StandardCapSpace = 2 + 1) := ⟨by simp [StandardCapSpace]⟩
  have hvec : ContMDiff (𝓡 3) (𝓡 3) ∞
      (fun x : U => ‖x.val‖⁻¹ • x.val) := by
    intro x
    apply (contMDiffAt_subtype_iff (U := U)
      (f := fun y : StandardCapSpace => ‖y‖⁻¹ • y)).mpr
    have hx : x.val ≠ 0 := x.property
    have h : ContDiffAt ℝ ∞ (fun y : StandardCapSpace => ‖y‖⁻¹ • y) x.val :=
      ((contDiffAt_norm ℝ hx).inv (norm_ne_zero_iff.mpr hx)).smul contDiffAt_id
    exact h.contMDiffAt
  have hmem : ∀ x : U, ‖x.val‖⁻¹ • x.val ∈ Metric.sphere (0 : StandardCapSpace) 1 := by
    intro x
    have hx : x.val ≠ 0 := x.property
    simp [norm_smul, norm_ne_zero_iff.mpr hx]
  have hsphere := hvec.codRestrict_sphere (n := 2) hmem
  have heq : (Set.codRestrict (fun x : U => ‖x.val‖⁻¹ • x.val) _ hmem) =
      (fun x : U => capUnitDirection x.val) := by
    funext x
    apply Subtype.ext
    exact (capUnitDirection_coe x.property).symm
  rw [heq] at hsphere
  intro x hx
  have h := hsphere.contMDiffAt (x := (⟨x, hx⟩ : U))
  exact (contMDiffAt_subtype_iff.mp h).contMDiffWithinAt



theorem exists_cap_sphere_shell {r : ℝ} (hr : 0 < r) {U : Set StandardCapSpace}
    (hU : IsOpen U) (hsub : Metric.sphere 0 r ⊆ U) :
    ∃ c : ℝ, 0 < c ∧ c < r ∧ {x : StandardCapSpace | r - c < ‖x‖ ∧ ‖x‖ < r + c} ⊆ U := by
  have hcompact := isCompact_sphere (0 : StandardCapSpace) r
  obtain ⟨d, hd, hthick⟩ := hcompact.exists_thickening_subset_open hU hsub
  obtain ⟨c, hc, hcmin⟩ := exists_between (lt_min hd hr)
  have hcd : c < d := hcmin.trans_le (min_le_left d r)
  have hcr : c < r := hcmin.trans_le (min_le_right d r)
  refine ⟨c, hc, hcr, ?_⟩
  intro x hx
  have hxn : 0 < ‖x‖ := by linarith [hx.1]
  have hnorm : ‖(capUnitDirection x).val‖ = 1 := by simp
  apply hthick
  rw [Metric.mem_thickening_iff]
  refine ⟨r • (capUnitDirection x).val, ?_, ?_⟩
  · simp [norm_smul, abs_of_pos hr, hnorm]
  · have heq : x - r • (capUnitDirection x).val =
        (‖x‖ - r) • (capUnitDirection x).val := by
      rw [sub_smul, capUnitDirection_radial]
    rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs, hnorm, mul_one, abs_lt]
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩


noncomputable def capShellMap (r c : ℝ) (z : RoundCylinderSpace) : StandardCapSpace :=
  (r - c * z.2) • z.1.val


noncomputable def capShellInverse (r c : ℝ) (x : StandardCapSpace) : RoundCylinderSpace :=
  (capUnitDirection x, (r - ‖x‖) / c)


theorem capShellMap_smooth (r c : ℝ) :
    ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ (capShellMap r c) := by
  let : Fact (Module.finrank ℝ StandardCapSpace = 2 + 1) := ⟨by simp [StandardCapSpace]⟩
  have hrad : ContDiff ℝ ∞ (fun s : ℝ => r - c * s) :=
    contDiff_const.sub (contDiff_const.mul contDiff_id)
  have hcoe : ContMDiff (𝓡 2) (𝓡 3) ∞ (fun z : UnitTwoSphere => z.val) :=
    contMDiff_coe_sphere
  exact (hrad.contMDiff.comp contMDiff_snd).smul (hcoe.comp contMDiff_fst)


theorem capShellInverse_smooth (r c : ℝ) :
    ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ (capShellInverse r c)
      ({0}ᶜ : Set StandardCapSpace) := by
  apply capUnitDirection_smooth.prodMk
  intro x hx
  have hnorm : ContDiffAt ℝ ∞ (fun y : StandardCapSpace => ‖y‖) x :=
    contDiffAt_norm ℝ hx
  exact ((contDiffAt_const.sub hnorm).div_const c).contMDiffAt.contMDiffWithinAt


theorem capShell_left_inverse {r c : ℝ} (hc : 0 < c) (hcr : c < r) :
    Set.LeftInvOn (capShellInverse r c) (capShellMap r c)
      (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1) := by
  rintro ⟨z, s⟩ hs
  have ht : 0 < r - c * s := by nlinarith [hs.2.2]
  apply Prod.ext
  · exact capUnitDirection_smul z ht
  · change (r - ‖(r - c * s) • z.val‖) / c = s
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht, show ‖z.val‖ = 1 by simp, mul_one]
    field_simp
    ring


theorem capShell_right_inverse {r c : ℝ} (hc : 0 < c) :
    Function.LeftInverse (capShellMap r c) (capShellInverse r c) := by
  intro x
  change (r - c * ((r - ‖x‖) / c)) • (capUnitDirection x).val = x
  rw [mul_div_cancel₀ _ hc.ne', sub_sub_cancel, capUnitDirection_radial]


theorem capShell_norm {r c : ℝ} (hc : 0 < c) (hcr : c < r)
    {z : RoundCylinderSpace} (hz : z ∈ Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1) :
    ‖capShellMap r c z‖ = r - c * z.2 := by
  have ht : 0 < r - c * z.2 := by nlinarith [hz.2.2]
  simp [capShellMap, norm_smul, abs_of_pos ht]


theorem capShell_mem {r c : ℝ} (hc : 0 < c) (hcr : c < r)
    {z : RoundCylinderSpace} (hz : z ∈ Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1) :
    r - c < ‖capShellMap r c z‖ ∧ ‖capShellMap r c z‖ < r + c := by
  rw [capShell_norm hc hcr hz]
  constructor <;> nlinarith [hz.2.1, hz.2.2]


theorem capShellInverse_mem {r c : ℝ} (hc : 0 < c) {x : StandardCapSpace}
    (hx : r - c < ‖x‖ ∧ ‖x‖ < r + c) :
    capShellInverse r c x ∈ Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1 := by
  refine ⟨Set.mem_univ _, ?_, ?_⟩
  · change -1 < (r - ‖x‖) / c
    exact (lt_div_iff₀ hc).mpr (by linarith [hx.2])
  · change (r - ‖x‖) / c < 1
    exact (div_lt_iff₀ hc).mpr (by linarith [hx.1])



noncomputable def capShellHomeomorph (r c : ℝ) (hc : 0 < c) (hcr : c < r) :
    (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1 : Set RoundCylinderSpace) ≃ₜ
      {x : StandardCapSpace | r - c < ‖x‖ ∧ ‖x‖ < r + c} where
  toFun := fun z => ⟨capShellMap r c z.val, capShell_mem hc hcr z.property⟩
  invFun := fun x => ⟨capShellInverse r c x.val, capShellInverse_mem hc x.property⟩
  left_inv := fun z => Subtype.ext (capShell_left_inverse hc hcr z.property)
  right_inv := fun x => Subtype.ext (capShell_right_inverse hc x.val)
  continuous_toFun := ((capShellMap_smooth r c).continuous.comp
    continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    have hsub : {x : StandardCapSpace | r - c < ‖x‖ ∧ ‖x‖ < r + c} ⊆ {0}ᶜ := by
      intro x hx
      have hnorm : 0 < ‖x‖ := by linarith [hx.1]
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using norm_pos_iff.mp hnorm
    exact ((capShellInverse_smooth r c).continuousOn.mono hsub).domRestrict.subtype_mk _


theorem capShell_openEmbedding {r c : ℝ} (hc : 0 < c) (hcr : c < r) :
    Topology.IsOpenEmbedding (fun z : (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1 :
      Set RoundCylinderSpace) => capShellMap r c z.val) := by
  have hopen : IsOpen {x : StandardCapSpace | r - c < ‖x‖ ∧ ‖x‖ < r + c} :=
    (isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)
  exact hopen.isOpenEmbedding_subtypeVal.comp (capShellHomeomorph r c hc hcr).isOpenEmbedding


theorem capShell_image {r c : ℝ} (hc : 0 < c) (hcr : c < r) :
    capShellMap r c '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1) =
      {x : StandardCapSpace | r - c < ‖x‖ ∧ ‖x‖ < r + c} := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact capShell_mem hc hcr hz
  · intro hx
    exact ⟨capShellInverse r c x, capShellInverse_mem hc hx, capShell_right_inverse hc x⟩

end PoincareConjecture.M38
