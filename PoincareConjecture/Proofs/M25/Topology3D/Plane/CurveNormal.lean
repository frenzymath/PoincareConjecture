import Mathlib.Analysis.Calculus.ContDiff.Comp
import PoincareConjecture.Proofs.M25.Topology3D.Plane.RadialExtension
import PoincareConjecture.Proofs.M25.Topology3D.Plane.SphereTangent
import PoincareConjecture.Proofs.M25.Topology3D.Plane.TubeInjectivity

set_option autoImplicit false

open Set Metric Function
open scoped Manifold ContDiff RealInnerProductSpace

namespace PoincareConjecture.M25.Topology3D

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [Fact (Module.finrank ℝ E = 2)]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def curveFamilyVelocity (o : Orientation ℝ E (Fin 2))
    (C : ℝ × E → F) (p : ℝ × E) : F :=
  fderiv ℝ (fun x => C (p.1, x)) p.2 (o.rightAngleRotation p.2)

theorem contDiffAt_curveFamilyVelocity (o : Orientation ℝ E (Fin 2))
    {C : ℝ × E → F} {p : ℝ × E} (hC : ContDiffAt ℝ ∞ C p) :
    ContDiffAt ℝ ∞ (curveFamilyVelocity o C) p := by
  have hU : ContDiffAt ℝ ∞ (fun u : (ℝ × E) × E => C (u.1.1, u.2))
      (p, p.2) :=
    hC.comp (p, p.2) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
  have hD : ContDiffAt ℝ ∞
      (fun u : ℝ × E => fderiv ℝ (fun x => C (u.1, x)) u.2) p :=
    hU.fderiv contDiffAt_snd (by simp)
  exact hD.clm_apply (o.rightAngleRotation.contDiff.contDiffAt.comp p contDiffAt_snd)

theorem contMDiff_curveFamilyVelocity_sphere (o : Orientation ℝ E (Fin 2))
    {C : ℝ × E → F}
    (hC : ContDiffOn ℝ ∞ C (univ ×ˢ ({0} : Set E)ᶜ)) :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, F) ∞
      (fun p : ℝ × sphere (0 : E) 1 => curveFamilyVelocity o C (p.1, (p.2 : E))) := by
  intro p
  have hp : (p.1, (p.2 : E)) ∈ univ ×ˢ ({0} : Set E)ᶜ :=
    ⟨mem_univ _, ne_zero_of_mem_unit_sphere p.2⟩
  have hV := contDiffAt_curveFamilyVelocity o
    (hC.contDiffAt ((isOpen_univ.prod isClosed_singleton.isOpen_compl).mem_nhds hp))
  exact hV.contMDiffAt.comp p
    (contMDiffAt_fst.prodMk_space
      ((contMDiff_coe_sphere (m := ∞) (n := 1)).contMDiffAt.comp p contMDiffAt_snd))

noncomputable def curveFamilyNormal (o : Orientation ℝ E (Fin 2))
    (C : ℝ × E → E) (p : ℝ × E) : E :=
  ‖curveFamilyVelocity o C p‖⁻¹ • o.rightAngleRotation (curveFamilyVelocity o C p)

theorem norm_curveFamilyNormal (o : Orientation ℝ E (Fin 2))
    (C : ℝ × E → E) (p : ℝ × E) (hv : curveFamilyVelocity o C p ≠ 0) :
    ‖curveFamilyNormal o C p‖ = 1 := by
  rw [curveFamilyNormal, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_nonneg (norm_nonneg _), o.rightAngleRotation.norm_map,
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]

theorem inner_curveFamilyNormal_velocity (o : Orientation ℝ E (Fin 2))
    (C : ℝ × E → E) (p : ℝ × E) :
    inner ℝ (curveFamilyNormal o C p) (curveFamilyVelocity o C p) = 0 := by
  rw [curveFamilyNormal, real_inner_smul_left, o.inner_rightAngleRotation_self, mul_zero]

theorem contDiffAt_curveFamilyNormal (o : Orientation ℝ E (Fin 2))
    {C : ℝ × E → E} {p : ℝ × E} (hC : ContDiffAt ℝ ∞ C p)
    (hv : curveFamilyVelocity o C p ≠ 0) :
    ContDiffAt ℝ ∞ (curveFamilyNormal o C) p := by
  have hV := contDiffAt_curveFamilyVelocity o hC
  exact (((contDiffAt_norm ℝ hv).comp p hV).inv (norm_ne_zero_iff.mpr hv)).smul
    (o.rightAngleRotation.contDiff.contDiffAt.comp p hV)

theorem curveFamilyVelocity_radial_ne_zero (o : Orientation ℝ E (Fin 2))
    (q0 : sphere (0 : E) 1) (c : ℝ → sphere (0 : E) 1 → F)
    (hc : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, F) ∞
      (fun p : ℝ × sphere (0 : E) 1 => c p.1 p.2))
    (z : ℝ) (q : sphere (0 : E) 1)
    (hi : Injective (mfderiv (𝓡 1) 𝓘(ℝ, F) (c z) q)) :
    curveFamilyVelocity o (radialFamilyExtension q0 c) (z, (q : E)) ≠ 0 := by
  apply fderiv_rightAngleRotation_ne_zero_of_sphere_immersion o q
    (hGc := fun p => radialFamilyExtension_apply_sphere q0 c z p) (hi := hi)
  have hC := contDiffOn_radialFamilyExtension q0 c hc
  have hp : (z, (q : E)) ∈ univ ×ˢ ({0} : Set E)ᶜ :=
    ⟨mem_univ _, ne_zero_of_mem_unit_sphere q⟩
  exact ((hC.contDiffAt ((isOpen_univ.prod isClosed_singleton.isOpen_compl).mem_nhds hp)).comp
    (q : E) (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)

theorem exists_radialFamilyVelocity_margin (o : Orientation ℝ E (Fin 2))
    (q0 : sphere (0 : E) 1) (c : ℝ → sphere (0 : E) 1 → F)
    (hc : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, F) ∞
      (fun p : ℝ × sphere (0 : E) 1 => c p.1 p.2))
    {a b : ℝ} (hab : a ≤ b)
    (hi : ∀ z ∈ Icc a b, ∀ q : sphere (0 : E) 1,
      Injective (mfderiv (𝓡 1) 𝓘(ℝ, F) (c z) q)) :
    ∃ d > 0, ∀ z ∈ Ioo (a - d) (b + d), ∀ q : sphere (0 : E) 1,
      curveFamilyVelocity o (radialFamilyExtension q0 c) (z, (q : E)) ≠ 0 := by
  have : FiniteDimensional ℝ E := FiniteDimensional.of_finrank_pos (by
    rw [show Module.finrank ℝ E = 2 from Fact.out]
    norm_num)
  let V : ℝ × sphere (0 : E) 1 → F := fun p =>
    curveFamilyVelocity o (radialFamilyExtension q0 c) (p.1, (p.2 : E))
  have hV : Continuous V := (contMDiff_curveFamilyVelocity_sphere o
    (contDiffOn_radialFamilyExtension q0 c hc)).continuous
  have hU : IsOpen {p | V p ≠ 0} := isOpen_ne_fun hV continuous_const
  have hK : Icc a b ×ˢ (univ : Set (sphere (0 : E) 1)) ⊆ {p | V p ≠ 0} := by
    intro p hp
    exact curveFamilyVelocity_radial_ne_zero o q0 c hc p.1 p.2 (hi p.1 hp.1 p.2)
  obtain ⟨A, B, hA, _, hIA, hUB, hAB⟩ :=
    generalized_tube_lemma isCompact_Icc isCompact_univ hU hK
  obtain ⟨d, hd, hdA⟩ := exists_interval_margin hab hA hIA
  refine ⟨d, hd, ?_⟩
  intro z hz q
  change (z, q) ∈ {p | V p ≠ 0}
  exact hAB ⟨hdA hz, hUB (mem_univ q)⟩

end PoincareConjecture.M25.Topology3D
