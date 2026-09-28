import PoincareConjecture.Proofs.M25.Topology3D.Space3.CofactorNormal
import PoincareConjecture.Proofs.M25.Topology3D.Space3.RadialSphereChart
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold InnerProductSpace Topology

namespace PoincareConjecture.M25.Topology3D

noncomputable def immersedSphereRadialExtension (j : UnitTwoSphere → E3) : E3 → E3 :=
  j ∘ sphereDirection

theorem immersedSphereRadialExtension_contDiffOn (j : UnitTwoSphere → E3)
    (hj : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ j) :
    ContDiffOn ℝ ∞ (immersedSphereRadialExtension j) ({0}ᶜ : Set E3) :=
  (hj.comp_contMDiffOn sphereDirection_contMDiffOn).contDiffOn

theorem immersedSphereRadialExtension_smul (j : UnitTwoSphere → E3) (p : UnitTwoSphere)
    {r : ℝ} (hr : 0 < r) : immersedSphereRadialExtension j (r • (p : E3)) = j p := by
  simp only [immersedSphereRadialExtension, Function.comp_apply, sphereDirection_smul p hr]

theorem immersedSphereRadialExtension_coe (j : UnitTwoSphere → E3) (p : UnitTwoSphere) :
    immersedSphereRadialExtension j (p : E3) = j p := by
  simpa only [one_smul] using immersedSphereRadialExtension_smul j p zero_lt_one

private theorem immersedSphereRadialExtension_differentiableAt (j : UnitTwoSphere → E3)
    (hj : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ j) (p : UnitTwoSphere) :
    DifferentiableAt ℝ (immersedSphereRadialExtension j) (p : E3) := by
  have hU : IsOpen ({0}ᶜ : Set E3) := isClosed_singleton.isOpen_compl
  exact ((immersedSphereRadialExtension_contDiffOn j hj).contDiffAt
    (hU.mem_nhds (ne_zero_of_mem_unit_sphere p))).differentiableAt (by simp)

theorem immersedSphereRadialExtension_fderiv_radial (j : UnitTwoSphere → E3)
    (hj : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ j) (p : UnitTwoSphere) :
    fderiv ℝ (immersedSphereRadialExtension j) (p : E3) (p : E3) = 0 := by
  have hJ := (immersedSphereRadialExtension_differentiableAt j hj p).hasFDerivAt
  have hJ' : HasFDerivAt (immersedSphereRadialExtension j)
      (fderiv ℝ (immersedSphereRadialExtension j) (p : E3)) ((1 : ℝ) • (p : E3)) := by
    simpa only [one_smul] using hJ
  have hray : HasDerivAt (fun r : ℝ => r • (p : E3)) (p : E3) 1 := by
    simpa only [one_smul, id_eq] using (hasDerivAt_id (1 : ℝ)).smul_const (p : E3)
  have hd := hJ'.comp_hasDerivAt 1 hray
  have heq : (fun r : ℝ => immersedSphereRadialExtension j (r • (p : E3))) =ᶠ[𝓝 1]
      fun _ => j p := by
    filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < 1 from zero_lt_one)]
      with r hr
    exact immersedSphereRadialExtension_smul j p hr
  exact hd.unique ((hasDerivAt_const (1 : ℝ) (j p)).congr_of_eventuallyEq heq)

theorem immersedSphereRadialExtension_fderiv_comp (j : UnitTwoSphere → E3)
    (hj : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ j) (p : UnitTwoSphere) :
    (fderiv ℝ (immersedSphereRadialExtension j) (p : E3)).comp
      (mvfderiv (𝓡 2) (fun q : UnitTwoSphere => (q : E3)) p) =
      mvfderiv (𝓡 2) j p := by
  let : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩
  have hi : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞
      (fun q : UnitTwoSphere => (q : E3)) := contMDiff_coe_sphere
  have hsame : immersedSphereRadialExtension j ∘ (fun q : UnitTwoSphere => (q : E3)) = j :=
    funext (immersedSphereRadialExtension_coe j)
  have hd := (immersedSphereRadialExtension_differentiableAt j hj p).hasFDerivAt.hasMFDerivAt.comp p
    (hi.mdifferentiable (by simp) p).hasMFDerivAt
  have hh := hd.mfderiv
  rw [hsame] at hh
  apply ContinuousLinearMap.ext
  intro v
  change fderiv ℝ (immersedSphereRadialExtension j) (p : E3)
      (mfderiv (𝓡 2) 𝓘(ℝ, E3) (fun q : UnitTwoSphere => (q : E3)) p v) =
    mfderiv (𝓡 2) 𝓘(ℝ, E3) j p v
  exact congrArg (fun A => A v) hh.symm

theorem immersedSphereRadialExtension_fderiv_injOn (j : UnitTwoSphere → E3)
    (hj : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ j)
    (hinj : ∀ p, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, E3) j p))
    (p : UnitTwoSphere) :
    Set.InjOn (fderiv ℝ (immersedSphereRadialExtension j) (p : E3))
      ((ℝ ∙ (p : E3))ᗮ : Set E3) := by
  let : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩
  let B := mvfderiv (𝓡 2) (fun q : UnitTwoSphere => (q : E3)) p
  have hrange : B.range = (ℝ ∙ (p : E3))ᗮ := range_mvfderiv_subtypeVal p
  intro x hx y hy hxy
  rw [← hrange] at hx hy
  obtain ⟨v, rfl⟩ := hx
  obtain ⟨w, rfl⟩ := hy
  apply congrArg B
  apply hinj p
  change mvfderiv (𝓡 2) j p v = mvfderiv (𝓡 2) j p w
  rw [← immersedSphereRadialExtension_fderiv_comp j hj p]
  exact hxy

theorem immersedSphereRadialExtension_fderiv_contMDiff (j : UnitTwoSphere → E3)
    (hj : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ j) :
    ContMDiff (𝓡 2) 𝓘(ℝ, E3 →L[ℝ] E3) ∞
      (fun p : UnitTwoSphere => fderiv ℝ (immersedSphereRadialExtension j) (p : E3)) := by
  let : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩
  have hU : IsOpen ({0}ᶜ : Set E3) := isClosed_singleton.isOpen_compl
  have hder : ContDiffOn ℝ ∞ (fderiv ℝ (immersedSphereRadialExtension j)) ({0}ᶜ : Set E3) :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen hU).mp
      (immersedSphereRadialExtension_contDiffOn j hj)).2
  have hi : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞
      (fun p : UnitTwoSphere => (p : E3)) := contMDiff_coe_sphere
  exact hder.contMDiffOn.comp_contMDiff hi ne_zero_of_mem_unit_sphere

noncomputable def immersedSphereRawNormal (j : UnitTwoSphere → E3)
    (p : UnitTwoSphere) : E3 :=
  cofactorNormal (fderiv ℝ (immersedSphereRadialExtension j) (p : E3)) (p : E3)

theorem immersedSphereRawNormal_contMDiff (j : UnitTwoSphere → E3)
    (hj : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ j) :
    ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ (immersedSphereRawNormal j) := by
  let : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩
  have hU : IsOpen ({0}ᶜ : Set E3) := isClosed_singleton.isOpen_compl
  have hder : ContDiffOn ℝ ∞ (fderiv ℝ (immersedSphereRadialExtension j)) ({0}ᶜ : Set E3) :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen hU).mp
      (immersedSphereRadialExtension_contDiffOn j hj)).2
  have hpair : ContDiffOn ℝ ∞
      (fun y : E3 => (fderiv ℝ (immersedSphereRadialExtension j) y, y)) ({0}ᶜ : Set E3) :=
    hder.prodMk contDiffOn_id
  have hraw := contDiff_cofactorNormal.comp_contDiffOn hpair
  have hi : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞
      (fun p : UnitTwoSphere => (p : E3)) := contMDiff_coe_sphere
  exact hraw.contMDiffOn.comp_contMDiff hi ne_zero_of_mem_unit_sphere

theorem immersedSphereRawNormal_nonzero_orthogonal (j : UnitTwoSphere → E3)
    (hj : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ j)
    (hinj : ∀ p, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, E3) j p))
    (p : UnitTwoSphere) :
    immersedSphereRawNormal j p ≠ 0 ∧
      ∀ v : TangentSpace (𝓡 2) p,
        ⟪immersedSphereRawNormal j p, mfderiv (𝓡 2) 𝓘(ℝ, E3) j p v⟫_ℝ = 0 := by
  obtain ⟨hn, horth⟩ := cofactorNormal_nonzero_orthogonal
    (fderiv ℝ (immersedSphereRadialExtension j) (p : E3)) (p : E3) (norm_eq_of_mem_sphere p)
    (immersedSphereRadialExtension_fderiv_radial j hj p)
    (immersedSphereRadialExtension_fderiv_injOn j hj hinj p)
  refine ⟨hn, ?_⟩
  intro v
  change ⟪immersedSphereRawNormal j p, mvfderiv (𝓡 2) j p v⟫_ℝ = 0
  rw [← immersedSphereRadialExtension_fderiv_comp j hj p]
  exact horth _

theorem exists_immersed_sphere_unit_normal (j : UnitTwoSphere → E3)
    (hj : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ j)
    (hinj : ∀ p, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, E3) j p)) :
    ∃ N : UnitTwoSphere → E3,
      ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ N ∧
      (∀ p, ‖N p‖ = 1) ∧
      ∀ (p : UnitTwoSphere) (v : TangentSpace (𝓡 2) p),
        ⟪N p, mfderiv (𝓡 2) 𝓘(ℝ, E3) j p v⟫_ℝ = 0 := by
  let : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩
  have hn (p : UnitTwoSphere) := immersedSphereRawNormal_nonzero_orthogonal j hj hinj p
  have hdir : ContMDiff (𝓡 2) (𝓡 2) ∞
      (fun p => sphereDirection (immersedSphereRawNormal j p)) :=
    sphereDirection_contMDiffOn.comp_contMDiff
      (immersedSphereRawNormal_contMDiff j hj) (fun p => (hn p).1)
  refine ⟨fun p => (sphereDirection (immersedSphereRawNormal j p) : E3),
    contMDiff_coe_sphere.comp hdir, ?_, ?_⟩
  · intro p
    exact norm_eq_of_mem_sphere _
  · intro p v
    change ⟪(sphereDirection (immersedSphereRawNormal j p) : E3),
      mvfderiv (𝓡 2) j p v⟫_ℝ = 0
    have horth : ⟪immersedSphereRawNormal j p, mvfderiv (𝓡 2) j p v⟫_ℝ = 0 := (hn p).2 v
    rw [sphereDirection_coe (hn p).1, NormedSpace.normalize, real_inner_smul_left,
      horth, mul_zero]

end PoincareConjecture.M25.Topology3D
