import PoincareConjecture.Proofs.M25.Topology3D.Space3.RadialSphereChart
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SardRegularValues
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions











set_option autoImplicit false

open Set Metric MeasureTheory
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D



noncomputable def sphereRadialExtension (N : UnitTwoSphere → UnitTwoSphere) (x : E3) : E3 :=
  ‖x‖ • (N (sphereDirection x) : E3)



theorem sphereRadialExtension_smul (N : UnitTwoSphere → UnitTwoSphere)
    (q : UnitTwoSphere) {r : ℝ} (hr : 0 < r) :
    sphereRadialExtension N (r • (q : E3)) = r • (N q : E3) := by
  rw [sphereRadialExtension, sphereDirection_smul q hr, norm_smul,
    Real.norm_eq_abs, abs_of_pos hr, norm_eq_of_mem_sphere, mul_one]


theorem sphereRadialExtension_contDiffOn (N : UnitTwoSphere → UnitTwoSphere)
    (hN : ContMDiff (𝓡 2) (𝓡 2) ∞ N) :
    ContDiffOn ℝ ∞ (sphereRadialExtension N) ({0}ᶜ : Set E3) := by
  let : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩
  have hn : ContDiffOn ℝ ∞ (fun x : E3 => ‖x‖) ({0}ᶜ : Set E3) :=
    fun x hx => (contDiffAt_norm ℝ (show x ≠ 0 from hx)).contDiffWithinAt
  exact (hn.contMDiffOn.smul (contMDiff_coe_sphere.comp_contMDiffOn
    (hN.comp_contMDiffOn sphereDirection_contMDiffOn))).contDiffOn



theorem sphere_mfderiv_injective_of_radialExtension
    (N : UnitTwoSphere → UnitTwoSphere) (hN : ContMDiff (𝓡 2) (𝓡 2) ∞ N)
    (q : UnitTwoSphere) {r : ℝ} (hr : 0 < r)
    (hG : Function.Injective (fderiv ℝ (sphereRadialExtension N) (r • (q : E3)))) :
    Function.Injective (mfderiv (𝓡 2) (𝓡 2) N q) := by
  let : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩
  let i : UnitTwoSphere → E3 := fun p => (p : E3)
  have hi (p : UnitTwoSphere) : MDifferentiableAt (𝓡 2) 𝓘(ℝ, E3) i p :=
    (contMDiff_coe_sphere : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ i).mdifferentiable (by simp) p
  have hx : r • (q : E3) ≠ 0 := smul_ne_zero hr.ne' (ne_zero_of_mem_unit_sphere q)
  have hdG := ((sphereRadialExtension_contDiffOn N hN).contDiffAt
    (isClosed_singleton.isOpen_compl.mem_nhds hx)).differentiableAt (by simp)
  have hleft := hdG.hasFDerivAt.hasMFDerivAt.comp q ((hi q).hasMFDerivAt.const_smul r)
  have hright := ((hi (N q)).hasMFDerivAt.const_smul r).comp q
    (hN.mdifferentiable (by simp) q).hasMFDerivAt
  have hformula : sphereRadialExtension N ∘ (r • i) = (r • i) ∘ N :=
    funext fun p => sphereRadialExtension_smul N p hr
  rw [hformula] at hleft
  have hderiv := hasMFDerivAt_unique hleft hright
  let A : TangentSpace (𝓡 2) q →L[ℝ] E3 := mfderiv (𝓡 2) 𝓘(ℝ, E3) i q
  let B : TangentSpace (𝓡 2) (N q) →L[ℝ] E3 := mfderiv (𝓡 2) 𝓘(ℝ, E3) i (N q)
  have hderiv' : (fderiv ℝ (sphereRadialExtension N) (r • (q : E3))).comp (r • A) =
      (r • B).comp (mfderiv (𝓡 2) (𝓡 2) N q) := hderiv
  intro a b hab
  have h : fderiv ℝ (sphereRadialExtension N) (r • (q : E3)) (r • A a) =
      r • B (mfderiv (𝓡 2) (𝓡 2) N q a) := congrArg (fun L => L a) hderiv'
  have h' : fderiv ℝ (sphereRadialExtension N) (r • (q : E3)) (r • A b) =
      r • B (mfderiv (𝓡 2) (𝓡 2) N q b) := congrArg (fun L => L b) hderiv'
  have hA : A a = A b := (smul_right_injective E3 hr.ne')
    (hG (h.trans ((congrArg (fun v => r • B v) hab).trans h'.symm)))
  exact injective_mvfderiv_subtypeVal_sphere q
    (congrArg (NormedSpace.fromTangentSpace (𝕜 := ℝ) (q : E3)) hA)



theorem exists_opposite_sphere_regularValues (N : UnitTwoSphere → UnitTwoSphere)
    (hN : ContMDiff (𝓡 2) (𝓡 2) ∞ N) :
    ∃ u : UnitTwoSphere, ∀ q : UnitTwoSphere,
      ((N q : E3) = (u : E3) ∨ (N q : E3) = -(u : E3)) →
        Function.Injective (mfderiv (𝓡 2) (𝓡 2) N q) := by
  have hU : IsOpen ({0}ᶜ : Set E3) := isClosed_singleton.isOpen_compl
  have hd := dense_opposite_regularValues volume (sphereRadialExtension N) ({0}ᶜ : Set E3)
    (fun x hx => ((sphereRadialExtension_contDiffOn N hN).contDiffAt
      (hU.mem_nhds hx)).differentiableAt (by simp))
  obtain ⟨z, hz⟩ := (NormedSpace.sphere_nonempty (E := E3) (x := 0)).mpr zero_le_one
  have hUnonempty : ({0}ᶜ : Set E3).Nonempty :=
    ⟨z, ne_zero_of_mem_unit_sphere (⟨z, hz⟩ : UnitTwoSphere)⟩
  obtain ⟨v, hv, hv0⟩ := hd.exists_mem_open hU hUnonempty
  have hr : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  refine ⟨sphereDirection v, ?_⟩
  intro q hq
  have hx : ‖v‖ • (q : E3) ≠ 0 := smul_ne_zero hr.ne' (ne_zero_of_mem_unit_sphere q)
  have hvec : ‖v‖ • (sphereDirection v : E3) = v := by
    rw [sphereDirection_coe hv0]
    exact NormedSpace.norm_smul_normalize v
  have hdet : (fderiv ℝ (sphereRadialExtension N) (‖v‖ • (q : E3))).det ≠ 0 := by
    rcases hq with hq | hq
    · apply hv.1 _ hx
      rw [sphereRadialExtension_smul N q hr, hq, hvec]
    · apply hv.2 _ hx
      rw [sphereRadialExtension_smul N q hr, hq, smul_neg, hvec]
  apply sphere_mfderiv_injective_of_radialExtension N hN q hr
  apply LinearMap.ker_eq_bot.mp
  by_contra hker
  exact hdet (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hker)

end PoincareConjecture.M25.Topology3D
