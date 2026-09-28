import PoincareConjecture.Proofs.M25.Topology3D.Plane.AngularCoherence
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.LocallyConvex.WithSeminorms

set_option autoImplicit false

open Set Metric Function Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M25.Topology3D

theorem exists_contDiff_sphere_parameter_lift
    {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : ℂ ≃ₗᵢ[ℝ] E) (γ : V → E) (hγ : ContDiff ℝ ∞ γ)
    (hnorm : ∀ x, ‖γ x‖ = 1) (x0 : V) (s0 : ℝ)
    (h0 : (sphereCircleParameter e s0 : E) = γ x0) :
    ∃ B : V → ℝ, ContDiff ℝ ∞ B ∧ B x0 = s0 ∧
      ∀ x, (sphereCircleParameter e (B x) : E) = γ x := by
  have hunit (x : V) : e.symm (γ x) ∈ Submonoid.unitSphere ℂ := by
    change e.symm (γ x) ∈ sphere (0 : ℂ) 1
    rw [mem_sphere_zero_iff_norm, e.symm.norm_map, hnorm]
  let f : C(V, Circle) :=
    ⟨fun x => ⟨e.symm (γ x), hunit x⟩,
      (e.symm.continuous.comp hγ.continuous).subtype_mk hunit⟩
  have he0 : Circle.exp s0 = f x0 := by
    apply Subtype.ext
    apply e.injective
    change e (Circle.exp s0 : ℂ) = e (e.symm (γ x0))
    rw [e.apply_symm_apply]
    exact h0
  obtain ⟨B, ⟨hB0, hBlift⟩, _⟩ :=
    Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts f x0 s0 he0
  have hBimage (x : V) : (sphereCircleParameter e (B x) : E) = γ x := by
    have h := congrArg (fun g : V → Circle => (g x : ℂ)) hBlift
    have he := congrArg e h
    change e (Circle.exp (B x) : ℂ) = e (e.symm (γ x)) at he
    rw [e.apply_symm_apply] at he
    exact he
  have hBsmooth : ContDiff ℝ ∞ (B : V → ℝ) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    let a := B x
    let C : V → ℝ := fun y => circleAngularCoordinate e (a, γ y)
    have hdom : (a, γ x) ∈
        {p : ℝ × E | e.symm p.2 * (Circle.exp (-p.1) : ℂ) ∈ Complex.slitPlane} := by
      rw [← hBimage x]
      exact sphereCircleParameter_mem_angularDomain e a a
        (by simp only [sub_self, mem_Ioo]; exact ⟨neg_neg_of_pos Real.pi_pos, Real.pi_pos⟩)
    have hangle : ContDiffAt ℝ ∞ (circleAngularCoordinate e) (a, γ x) :=
      (contDiffOn_circleAngularCoordinate e).contDiffAt
        ((isOpen_circleAngularCoordinate_domain e).mem_nhds hdom)
    have hC : ContDiffAt ℝ ∞ C x :=
      ContDiffAt.comp (g := circleAngularCoordinate e) (f := fun y : V => (a, γ y)) x hangle
        ((contDiffAt_const (c := a)).prodMk hγ.contDiffAt)
    have hCx : C x = B x := by
      dsimp only [C]
      rw [← hBimage x]
      exact circleAngularCoordinate_sphereCircleParameter e a a
        (by simp only [sub_self, mem_Ioc]; exact ⟨neg_neg_of_pos Real.pi_pos, Real.pi_pos.le⟩)
    have hsame (y : V) : sphereCircleParameter e (B y) = sphereCircleParameter e (C y) := by
      let q : sphere (0 : E) 1 := ⟨γ y, mem_sphere_zero_iff_norm.mpr (hnorm y)⟩
      have hq : sphereCircleParameter e (C y) = q :=
        sphereCircleParameter_circleAngularCoordinate e a q
      apply Subtype.ext
      rw [hBimage y, hq]
    have heq : (B : V → ℝ) =ᶠ[𝓝 x] C :=
      eventuallyEq_of_sphereCircleParameter_eq e B.continuous.continuousAt hC.continuousAt
        hCx.symm (Eventually.of_forall hsame)
    exact hC.congr_of_eventuallyEq heq
  exact ⟨B, hBsmooth, hB0, hBimage⟩

end PoincareConjecture.M25.Topology3D
