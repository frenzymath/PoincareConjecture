import PoincareConjecture.Proofs.Horizon.Topology.Homotopy.Extension.BallHomotopyExtension
import PoincareConjecture.Proofs.Horizon.Topology.Homotopy.Cube.CubeSphere







set_option autoImplicit false

open Set Metric Topology
open scoped unitInterval

namespace Poincare.Topology


theorem exists_cube_homotopy_extension
    {N X : Type*} [Finite N] [TopologicalSpace X]
    (f : C(I^N, X)) (h : C(unitInterval × Cube.boundary N, X))
    (hh : ∀ x : Cube.boundary N, h (0, x) = f x) :
    ∃ F : C(unitInterval × (I^N), X),
      (∀ x, F (0, x) = f x) ∧
      ∀ t (x : Cube.boundary N), F (t, x) = h (t, x) := by
  let := Fintype.ofFinite N
  obtain ⟨e, _, he⟩ := exists_cube_closedBall_homeomorph (N := N)
  let inclusion : C(sphere (0 : N → ℝ) 1, closedBall (0 : N → ℝ) 1) :=
    ⟨fun x => ⟨x, sphere_subset_closedBall x.property⟩,
      continuous_subtype_val.subtype_mk _⟩
  have hb (x : sphere (0 : N → ℝ) 1) : e.symm (inclusion x) ∈ Cube.boundary N := by
    apply (he _).mpr
    rw [e.apply_symm_apply]
    exact mem_sphere_zero_iff_norm.mp x.property
  let boundaryMap : C(sphere (0 : N → ℝ) 1, Cube.boundary N) :=
    ⟨fun x => ⟨e.symm (inclusion x), hb x⟩,
      (e.symm.continuous.comp inclusion.continuous).subtype_mk hb⟩
  let g := f.comp ⟨e.symm, e.symm.continuous⟩
  let side : C(unitInterval × sphere (0 : N → ℝ) 1, X) :=
    h.comp ⟨fun z => (z.1, boundaryMap z.2),
      continuous_fst.prodMk (boundaryMap.continuous.comp continuous_snd)⟩
  have hstart (x : sphere (0 : N → ℝ) 1) : side (0, x) = g (inclusion x) :=
    hh (boundaryMap x)
  obtain ⟨F, hF0, hFS⟩ := exists_closedBall_homotopy_extension g side hstart
  let cylinderMap : C(unitInterval × (I^N), unitInterval × closedBall (0 : N → ℝ) 1) :=
    ⟨fun z => (z.1, e z.2), continuous_fst.prodMk (e.continuous.comp continuous_snd)⟩
  refine ⟨F.comp cylinderMap, ?_, ?_⟩
  · intro z
    change F (0, e z) = f z
    exact (hF0 (e z)).trans (congrArg f (e.symm_apply_apply z))
  · intro t z
    let spherePoint : sphere (0 : N → ℝ) 1 :=
      ⟨e z, mem_sphere_zero_iff_norm.mpr ((he z).mp z.property)⟩
    have hi : inclusion spherePoint = e z := rfl
    have hboundary : boundaryMap spherePoint = z := by
      apply Subtype.ext
      change e.symm (inclusion spherePoint) = z.val
      rw [hi, e.symm_apply_apply]
    change F (t, e z) = h (t, z)
    have hside := hFS t spherePoint
    change F (t, inclusion spherePoint) = h (t, boundaryMap spherePoint) at hside
    simpa only [hi, hboundary] using hside


theorem exists_cube_cylinder_homeomorph (N : Type*) :
    ∃ e : (unitInterval × (I^N)) ≃ₜ (I^(Option N)),
      (∀ z, e z none = z.1) ∧
      (∀ z i, e z (some i) = z.2 i) ∧
      ∀ z, e z ∈ Cube.boundary (Option N) ↔
        z.1 = 0 ∨ z.1 = 1 ∨ z.2 ∈ Cube.boundary N := by
  let e : (unitInterval × (I^N)) ≃ₜ (I^(Option N)) := {
    toFun := fun z i => i.elim z.1 z.2
    invFun := fun v => (v none, fun i => v (some i))
    left_inv := fun _ => rfl
    right_inv := by
      intro v
      funext i
      cases i <;> rfl
    continuous_toFun := continuous_pi fun i => by
      cases i with
      | none => exact continuous_fst
      | some i => exact (continuous_apply i).comp continuous_snd
    continuous_invFun := (continuous_apply none).prodMk
      (continuous_pi fun i => continuous_apply (some i))
  }
  refine ⟨e, fun _ => rfl, fun _ _ => rfl, ?_⟩
  intro z
  constructor
  · rintro ⟨i, hi⟩
    cases i with
    | none => exact hi.elim Or.inl (fun h => Or.inr (Or.inl h))
    | some i => exact Or.inr (Or.inr ⟨i, hi⟩)
  · rintro (h | h | ⟨i, hi⟩)
    · exact ⟨none, Or.inl h⟩
    · exact ⟨none, Or.inr h⟩
    · exact ⟨some i, hi⟩

end Poincare.Topology
