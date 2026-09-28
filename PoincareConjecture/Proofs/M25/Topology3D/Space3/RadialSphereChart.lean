import PoincareConjecture.Proofs.M25.Topology3D.Services
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SphereSmoothRestriction
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Module.Normalize











set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.M25.Topology3D



noncomputable def sphereDirection (x : E3) : UnitTwoSphere :=
  if hx : x = 0 then
    Classical.choice ((NormedSpace.sphere_nonempty (E := E3) (x := 0)).mpr zero_le_one).coe_sort
  else ⟨NormedSpace.normalize x, mem_sphere_zero_iff_norm.mpr (NormedSpace.norm_normalize hx)⟩


theorem sphereDirection_coe {x : E3} (hx : x ≠ 0) :
    (sphereDirection x : E3) = NormedSpace.normalize x := by
  simp only [sphereDirection, dif_neg hx]


theorem sphereDirection_smul (q : UnitTwoSphere) {r : ℝ} (hr : 0 < r) :
    sphereDirection (r • (q : E3)) = q := by
  apply Subtype.ext
  rw [sphereDirection_coe (smul_ne_zero hr.ne' (ne_zero_of_mem_unit_sphere q)),
    NormedSpace.normalize_smul_of_pos hr,
    NormedSpace.normalize_eq_self_of_norm_eq_one (norm_eq_of_mem_sphere q)]


theorem sphereDirection_contMDiffOn :
    ContMDiffOn 𝓘(ℝ, E3) (𝓡 2) ∞ sphereDirection ({0}ᶜ : Set E3) := by
  let : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩
  have hU : IsOpen ({0}ᶜ : Set E3) := isClosed_singleton.isOpen_compl
  have hnormalize : ContDiffOn ℝ ∞ (NormedSpace.normalize : E3 → E3) ({0}ᶜ : Set E3) := by
    intro x hx
    have hx0 : x ≠ 0 := hx
    exact (((contDiffAt_norm ℝ hx0).inv (norm_ne_zero_iff.mpr hx0)).smul
      contDiffAt_id).contDiffWithinAt
  have hcoe : ContDiffOn ℝ ∞ (fun x => (sphereDirection x : E3)) ({0}ᶜ : Set E3) :=
    hnormalize.congr (fun x hx => sphereDirection_coe hx)
  exact contMDiffOn_sphere_of_coe hU sphereDirection hcoe.contMDiffOn


noncomputable def radialSphereMap (p : UnitTwoSphere × ℝ) : E3 := p.2 • (p.1 : E3)


theorem radialSphereMap_contMDiff :
    ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E3) ∞ radialSphereMap := by
  let : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩
  exact contMDiff_snd.smul (contMDiff_coe_sphere.comp contMDiff_fst)


theorem radialSphereInverse_contMDiffOn :
    ContMDiffOn 𝓘(ℝ, E3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
      (fun x => (sphereDirection x, ‖x‖)) ({0}ᶜ : Set E3) := by
  apply sphereDirection_contMDiffOn.prodMk
  apply ContDiffOn.contMDiffOn
  intro x hx
  exact (contDiffAt_norm ℝ (show x ≠ 0 from hx)).contDiffWithinAt


noncomputable def radialSphereChart : OpenPartialHomeomorph (UnitTwoSphere × ℝ) E3 where
  toFun := radialSphereMap
  invFun := fun x => (sphereDirection x, ‖x‖)
  source := univ ×ˢ Ioi 0
  target := {0}ᶜ
  map_source' p hp := smul_ne_zero (ne_of_gt hp.2) (ne_zero_of_mem_unit_sphere p.1)
  map_target' x hx := ⟨mem_univ _, norm_pos_iff.mpr hx⟩
  left_inv' p hp := by
    apply Prod.ext
    · exact sphereDirection_smul p.1 hp.2
    · simp only [radialSphereMap, norm_smul, Real.norm_eq_abs,
        abs_of_pos (show (0 : ℝ) < p.2 from hp.2), norm_eq_of_mem_sphere, mul_one]
  right_inv' x hx := by
    change ‖x‖ • (sphereDirection x : E3) = x
    rw [sphereDirection_coe hx]
    exact NormedSpace.norm_smul_normalize x
  open_source := isOpen_univ.prod isOpen_Ioi
  open_target := isClosed_singleton.isOpen_compl
  continuousOn_toFun := radialSphereMap_contMDiff.continuous.continuousOn
  continuousOn_invFun := radialSphereInverse_contMDiffOn.continuousOn

end PoincareConjecture.M25.Topology3D
