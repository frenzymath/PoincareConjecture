import PoincareConjecture.Proofs.M25.Topology3D.Space3.RadialSphereChart
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

theorem sphere_mvfderiv_inner_apply (f g : UnitTwoSphere → E3) (q : UnitTwoSphere)
    (hf : MDifferentiableAt (𝓡 2) 𝓘(ℝ, E3) f q)
    (hg : MDifferentiableAt (𝓡 2) 𝓘(ℝ, E3) g q) (a : TangentSpace (𝓡 2) q) :
    mvfderiv (𝓡 2) (fun p => ⟪f p, g p⟫_ℝ) q a =
      ⟪f q, mvfderiv (𝓡 2) g q a⟫_ℝ + ⟪mvfderiv (𝓡 2) f q a, g q⟫_ℝ := by
  have hd := ((isBoundedBilinearMap_inner (𝕜 := ℝ) (E := E3)).hasFDerivAt
    (f q, g q)).hasMFDerivAt.comp q (hf.hasMFDerivAt.prodMk hg.hasMFDerivAt)
  exact congrArg (fun L : TangentSpace (𝓡 2) q →L[ℝ] ℝ => L a) hd.mfderiv

theorem sphere_height_critical_pairing (e : UnitTwoSphere → E3)
    (he : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ e) (q : UnitTwoSphere) (u : E3)
    (hcritical : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun p => ⟪u, e p⟫_ℝ) q = 0)
    (a : TangentSpace (𝓡 2) q) : ⟪u, mvfderiv (𝓡 2) e q a⟫_ℝ = 0 := by
  have hd := (InnerProductSpace.toDual ℝ E3 u).hasFDerivAt.hasMFDerivAt.comp q
    (he.mdifferentiable (by simp) q).hasMFDerivAt
  have h : (InnerProductSpace.toDual ℝ E3 u).comp (mvfderiv (𝓡 2) e q) = 0 :=
    hd.mfderiv.symm.trans hcritical
  exact congrArg (fun L : TangentSpace (𝓡 2) q →L[ℝ] ℝ => L a) h

theorem criticalBranch_height_mvfderiv (e : UnitTwoSphere → E3)
    (he : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ e) (g : UnitTwoSphere → UnitTwoSphere)
    (q : UnitTwoSphere) (hg : MDifferentiableAt (𝓡 2) (𝓡 2) g q)
    (hcritical : mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
      (fun p => ⟪(q : E3), e p⟫_ℝ) (g q) = 0) (a : TangentSpace (𝓡 2) q) :
    mvfderiv (𝓡 2) (fun p : UnitTwoSphere => ⟪(p : E3), e (g p)⟫_ℝ) q a =
      ⟪mvfderiv (𝓡 2) (fun p : UnitTwoSphere => (p : E3)) q a, e (g q)⟫_ℝ := by
  let : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩
  have hi : MDifferentiableAt (𝓡 2) 𝓘(ℝ, E3)
      (fun p : UnitTwoSphere => (p : E3)) q :=
    (contMDiff_coe_sphere : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ _).mdifferentiable (by simp) q
  have heg := (he.mdifferentiable (by simp) (g q)).comp q hg
  have hcomp : mvfderiv (𝓡 2) (e ∘ g) q =
      (mvfderiv (𝓡 2) e (g q)).comp (mfderiv (𝓡 2) (𝓡 2) g q) :=
    mfderiv_comp q (he.mdifferentiable (by simp) (g q)) hg
  have hinner :
      mvfderiv (𝓡 2) (fun p : UnitTwoSphere => ⟪(p : E3), e (g p)⟫_ℝ) q a =
        ⟪(q : E3), mvfderiv (𝓡 2) (e ∘ g) q a⟫_ℝ +
          ⟪mvfderiv (𝓡 2) (fun p : UnitTwoSphere => (p : E3)) q a, e (g q)⟫_ℝ :=
    sphere_mvfderiv_inner_apply (fun p : UnitTwoSphere => (p : E3)) (e ∘ g) q hi heg a
  rw [hinner, hcomp]
  have hz := sphere_height_critical_pairing e he (g q) (q : E3) hcritical
    (mfderiv (𝓡 2) (𝓡 2) g q a)
  exact (congrArg (fun t : ℝ =>
    t + ⟪mvfderiv (𝓡 2) (fun p : UnitTwoSphere => (p : E3)) q a, e (g q)⟫_ℝ)
    hz).trans (zero_add _)

theorem criticalBranch_height_difference_nonzero (e : UnitTwoSphere → E3)
    (he : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ e) (hinj : Function.Injective e)
    (g k : UnitTwoSphere → UnitTwoSphere) (q : UnitTwoSphere)
    (hg : MDifferentiableAt (𝓡 2) (𝓡 2) g q)
    (hk : MDifferentiableAt (𝓡 2) (𝓡 2) k q)
    (hgc : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun p => ⟪(q : E3), e p⟫_ℝ) (g q) = 0)
    (hkc : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun p => ⟪(q : E3), e p⟫_ℝ) (k q) = 0)
    (hne : g q ≠ k q) (heq : ⟪(q : E3), e (g q)⟫_ℝ = ⟪(q : E3), e (k q)⟫_ℝ) :
    mvfderiv (𝓡 2) (fun p : UnitTwoSphere =>
      ⟪(p : E3), e (g p)⟫_ℝ - ⟪(p : E3), e (k p)⟫_ℝ) q ≠ 0 := by
  let : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩
  let i : UnitTwoSphere → E3 := fun p => (p : E3)
  have hi : MDifferentiableAt (𝓡 2) 𝓘(ℝ, E3) i q :=
    (contMDiff_coe_sphere : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ i).mdifferentiable (by simp) q
  have hgd := (he.mdifferentiable (by simp) (g q)).comp q hg
  have hkd := (he.mdifferentiable (by simp) (k q)).comp q hk
  have hH (l : UnitTwoSphere → E3) (hl : MDifferentiableAt (𝓡 2) 𝓘(ℝ, E3) l q) :
      MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ)
        (fun p : UnitTwoSphere => ⟪(p : E3), l p⟫_ℝ) q :=
    (((isBoundedBilinearMap_inner (𝕜 := ℝ) (E := E3)).hasFDerivAt
      (i q, l q)).hasMFDerivAt.comp q (hi.hasMFDerivAt.prodMk hl.hasMFDerivAt)).mdifferentiableAt
  let z := e (g q) - e (k q)
  have hz : z ∈ (ℝ ∙ (q : E3))ᗮ := by
    apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
    change ⟪(q : E3), e (g q) - e (k q)⟫_ℝ = 0
    rw [inner_sub_right, heq, sub_self]
  rw [← range_mvfderiv_subtypeVal (n := 2) q] at hz
  obtain ⟨a, ha⟩ := hz
  change mvfderiv (𝓡 2) i q a = z at ha
  intro hzero
  have hv : mvfderiv (𝓡 2) (fun p : UnitTwoSphere =>
      ⟪(p : E3), e (g p)⟫_ℝ - ⟪(p : E3), e (k p)⟫_ℝ) q a = 0 :=
    congrArg (fun L : TangentSpace (𝓡 2) q →L[ℝ] ℝ => L a) hzero
  have hsub := congrArg (fun L : TangentSpace (𝓡 2) q →L[ℝ] ℝ => L a)
    (mvfderiv_fun_sub (hH (e ∘ g) hgd) (hH (e ∘ k) hkd))
  have hv : mvfderiv (𝓡 2) (fun p : UnitTwoSphere => ⟪(p : E3), e (g p)⟫_ℝ) q a -
      mvfderiv (𝓡 2) (fun p : UnitTwoSphere => ⟪(p : E3), e (k p)⟫_ℝ) q a = 0 :=
    hsub.symm.trans hv
  rw [criticalBranch_height_mvfderiv e he g q hg hgc a,
    criticalBranch_height_mvfderiv e he k q hk hkc a, ← inner_sub_right] at hv
  change ⟪mvfderiv (𝓡 2) i q a, z⟫_ℝ = 0 at hv
  rw [ha] at hv
  exact hne (hinj (sub_eq_zero.mp ((inner_self_eq_zero (𝕜 := ℝ)).mp hv)))

end PoincareConjecture.M25.Topology3D
