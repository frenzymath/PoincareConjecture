import PoincareConjecture.Proofs.M25.Topology3D.Services
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SphereSmoothRestriction
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Module.Normalize













set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D



noncomputable def circleDirection (x : E2) : UnitCircle :=
  if hx : x = 0 then
    Classical.choice ((NormedSpace.sphere_nonempty (E := E2) (x := 0)).mpr zero_le_one).coe_sort
  else ⟨NormedSpace.normalize x, mem_sphere_zero_iff_norm.mpr (NormedSpace.norm_normalize hx)⟩


theorem circleDirection_coe {x : E2} (hx : x ≠ 0) :
    (circleDirection x : E2) = NormedSpace.normalize x := by
  simp only [circleDirection, dif_neg hx]


theorem circleDirection_smul (q : UnitCircle) {r : ℝ} (hr : 0 < r) :
    circleDirection (r • (q : E2)) = q := by
  apply Subtype.ext
  rw [circleDirection_coe (smul_ne_zero hr.ne' (ne_zero_of_mem_unit_sphere q)),
    NormedSpace.normalize_smul_of_pos hr,
    NormedSpace.normalize_eq_self_of_norm_eq_one (norm_eq_of_mem_sphere q)]


@[simp] theorem circleDirection_coe_unit (q : UnitCircle) :
    circleDirection (q : E2) = q := by
  simpa only [one_smul] using circleDirection_smul q (r := 1) zero_lt_one


theorem circleDirection_norm_smul (x : E2) : ‖x‖ • (circleDirection x : E2) = x := by
  by_cases hx : x = 0
  · subst x
    simp only [norm_zero, zero_smul]
  · rw [circleDirection_coe hx]
    exact NormedSpace.norm_smul_normalize x


theorem circleDirection_contMDiffOn :
    ContMDiffOn 𝓘(ℝ, E2) (𝓡 1) ∞ circleDirection ({0}ᶜ : Set E2) := by
  let : Fact (Module.finrank ℝ E2 = 1 + 1) := ⟨by simp [E2]⟩
  have hU : IsOpen ({0}ᶜ : Set E2) := isClosed_singleton.isOpen_compl
  have hnormalize : ContDiffOn ℝ ∞ (NormedSpace.normalize : E2 → E2) ({0}ᶜ : Set E2) := by
    intro x hx
    have hx0 : x ≠ 0 := hx
    exact (((contDiffAt_norm ℝ hx0).inv (norm_ne_zero_iff.mpr hx0)).smul
      contDiffAt_id).contDiffWithinAt
  have hcoe : ContDiffOn ℝ ∞ (fun x => (circleDirection x : E2)) ({0}ᶜ : Set E2) :=
    hnormalize.congr (fun x hx => circleDirection_coe hx)
  exact contMDiffOn_sphere_of_coe hU circleDirection hcoe.contMDiffOn


noncomputable def circleRadialMap (p : UnitCircle × ℝ) : E2 := p.2 • (p.1 : E2)


@[simp] theorem circleRadialMap_norm (p : UnitCircle × ℝ) :
    ‖circleRadialMap p‖ = |p.2| := by
  simp only [circleRadialMap, norm_smul, Real.norm_eq_abs, norm_eq_of_mem_sphere, mul_one]


theorem circleRadialMap_contMDiff :
    ContMDiff ((𝓡 1).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E2) ∞ circleRadialMap := by
  let : Fact (Module.finrank ℝ E2 = 1 + 1) := ⟨by simp [E2]⟩
  exact contMDiff_snd.smul (contMDiff_coe_sphere.comp contMDiff_fst)


theorem circleRadialInverse_contMDiffOn :
    ContMDiffOn 𝓘(ℝ, E2) ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞
      (fun x => (circleDirection x, ‖x‖)) ({0}ᶜ : Set E2) := by
  apply circleDirection_contMDiffOn.prodMk
  apply ContDiffOn.contMDiffOn
  intro x hx
  exact (contDiffAt_norm ℝ (show x ≠ 0 from hx)).contDiffWithinAt



noncomputable def circleRadialChart : OpenPartialHomeomorph (UnitCircle × ℝ) E2 where
  toFun := circleRadialMap
  invFun := fun x => (circleDirection x, ‖x‖)
  source := univ ×ˢ Ioi 0
  target := {0}ᶜ
  map_source' p hp := smul_ne_zero (ne_of_gt hp.2) (ne_zero_of_mem_unit_sphere p.1)
  map_target' x hx := ⟨mem_univ _, norm_pos_iff.mpr hx⟩
  left_inv' p hp := by
    apply Prod.ext
    · exact circleDirection_smul p.1 hp.2
    · exact (circleRadialMap_norm p).trans (abs_of_pos hp.2)
  right_inv' x _ := circleDirection_norm_smul x
  open_source := isOpen_univ.prod isOpen_Ioi
  open_target := isClosed_singleton.isOpen_compl
  continuousOn_toFun := circleRadialMap_contMDiff.continuous.continuousOn
  continuousOn_invFun := circleRadialInverse_contMDiffOn.continuousOn


@[simp] theorem circleRadialChart_apply (p : UnitCircle × ℝ) :
    circleRadialChart p = p.2 • (p.1 : E2) := rfl


@[simp] theorem circleRadialChart_symm_apply (x : E2) :
    circleRadialChart.symm x = (circleDirection x, ‖x‖) := rfl


@[simp] theorem circleRadialChart_source :
    circleRadialChart.source = (univ : Set UnitCircle) ×ˢ Ioi (0 : ℝ) := rfl


@[simp] theorem circleRadialChart_target : circleRadialChart.target = ({0}ᶜ : Set E2) := rfl


theorem circleRadialChart_contMDiffOn :
    ContMDiffOn ((𝓡 1).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E2) ∞
      circleRadialChart circleRadialChart.source :=
  circleRadialMap_contMDiff.contMDiffOn


theorem circleRadialChart_symm_contMDiffOn :
    ContMDiffOn 𝓘(ℝ, E2) ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞
      circleRadialChart.symm circleRadialChart.target :=
  circleRadialInverse_contMDiffOn

end PoincareConjecture.M25.Topology3D
