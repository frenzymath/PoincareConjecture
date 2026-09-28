import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Calculus.RadialExtension
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.InverseFunction.LocalDiffeomorph
import Mathlib.Analysis.Calculus.TangentCone.Real



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Reverse

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1
private instance : Fact (Module.finrank Real E3 = 2 + 1) := ⟨by simp⟩





theorem exists_spherical_marking_on_closedBall
    (G : E2 → E3) (hG : ContDiff Real ∞ G)
    (hGi : InjOn G (closedBall (0 : E2) 1))
    (hGder : ∀ x ∈ closedBall (0 : E2) 1, Injective (fderiv Real G x))
    (hmem : ∀ x ∈ closedBall (0 : E2) 1, G x ∈ sphere (0 : E3) 1)
    (p0 : S2) :
    ∃ m : E2 → S2,
      (∀ x ∈ closedBall (0 : E2) 1, (m x : E3) = G x) ∧
      InjOn m (closedBall 0 1) ∧
      ∀ x ∈ closedBall (0 : E2) 1,
        IsLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ m x := by
  let m : E2 → S2 := Plane.unitRadialProjection p0 ∘ G
  let N : E2 → E3 := fun x => m x
  let U : Set E2 := G ⁻¹' ({0} : Set E3)ᶜ
  have hU : IsOpen U := isClosed_singleton.isOpen_compl.preimage hG.continuous
  have hballU : closedBall (0 : E2) 1 ⊆ U := by
    intro x hx
    exact ne_zero_of_mem_unit_sphere ⟨G x, hmem x hx⟩
  have hm : ContMDiffOn (𝓡 2) (𝓡 2) ∞ m U :=
    (Plane.contMDiffOn_unitRadialProjection (n := 2) (m := ∞) p0).comp
      hG.contMDiff.contMDiffOn (fun _ hx => hx)
  have hN : ContDiffOn Real ∞ N U :=
    (contMDiff_coe_sphere.comp_contMDiffOn hm).contDiffOn
  have heq : EqOn N G (closedBall (0 : E2) 1) := by
    intro x hx
    exact congrArg Subtype.val
      (Plane.unitRadialProjection_apply_coe p0 ⟨G x, hmem x hx⟩)
  have hUD : UniqueDiffOn Real (closedBall (0 : E2) 1) :=
    uniqueDiffOn_convex (convex_closedBall (0 : E2) 1) (by
      rw [interior_closedBall (0 : E2) (by norm_num : (1 : Real) ≠ 0)]
      exact ⟨0, mem_ball_self (by norm_num)⟩)
  have hder (x : E2) (hx : x ∈ closedBall (0 : E2) 1) :
      fderiv Real N x = fderiv Real G x := by
    rw [← fderivWithin_eq_fderiv (hUD x hx)
      ((hN.contDiffAt (hU.mem_nhds (hballU hx))).differentiableAt (by simp)),
      ← fderivWithin_eq_fderiv (hUD x hx) (hG.differentiable (by simp) x)]
    exact fderivWithin_congr' heq hx
  let V : Set E2 := U ∩ {x | Injective (fderiv Real N x)}
  have hV : IsOpen V :=
    (hN.continuousOn_fderiv_of_isOpen hU (by simp)).isOpen_inter_preimage
      hU ContinuousLinearMap.isOpen_injective
  have hballV : closedBall (0 : E2) 1 ⊆ V := by
    intro x hx
    refine ⟨hballU hx, ?_⟩
    change Injective (fderiv Real N x)
    rw [hder x hx]
    exact hGder x hx
  have hbij (x : E2) (hx : x ∈ V) : Bijective (mfderiv (𝓡 2) (𝓡 2) m x) := by
    have hmx := hm.contMDiffAt (hU.mem_nhds hx.1)
    have hchain := mfderiv_comp x
      ((contMDiff_coe_sphere (n := 2) (m := ∞) (m x)).mdifferentiableAt (by simp))
      (hmx.mdifferentiableAt (by simp))
    have hinj : Injective (mfderiv (𝓡 2) (𝓡 2) m x) := by
      intro u w huw
      apply hx.2
      have hder' : fderiv Real N x =
          (mfderiv (𝓡 2) (𝓡 3) (fun p : S2 => (p : E3)) (m x)).comp
            (mfderiv (𝓡 2) (𝓡 2) m x) := by
        rw [← mfderiv_eq_fderiv]
        exact hchain
      rw [hder']
      exact congrArg (mfderiv (𝓡 2) (𝓡 3) (fun p : S2 => (p : E3)) (m x)) huw
    exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (V := E2) (V₂ := E2)
      (f := (mfderiv (𝓡 2) (𝓡 2) m x).toLinearMap) rfl).mp hinj⟩
  have hlocal := Poincare.isLocalDiffeomorphOn_of_contMDiffOn_bijective_mfderiv
    hV (hm.mono inter_subset_left) hbij
  refine ⟨m, heq, ?_, fun x hx => hlocal ⟨x, hballV hx⟩⟩
  intro x hx y hy hxy
  apply hGi hx hy
  rw [← heq hx, ← heq hy]
  exact congrArg Subtype.val hxy

end Poincare.Manifold.Schoenflies.Reverse
