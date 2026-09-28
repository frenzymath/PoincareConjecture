import PoincareConjecture.Proofs.M76.Brown.LocallyFlatEndQuotient
import PoincareConjecture.Proofs.M76.Brown.ExceptionalFibers.SphereRegionCancellation
import Mathlib.Topology.Compactification.OnePoint.Sphere

set_option autoImplicit false

open Set Metric
open scoped OnePoint

namespace PoincareConjecture.M76.LocallyFlatTopologicalSphere

local notation "V3" => (Fin 3 → ℝ)
local notation "X3" => OnePoint V3
local notation "S3" => sphere (0 : EuclideanSpace ℝ (Fin 4)) 1

theorem exists_compactified_ball_homeomorph {S : Set V3}
    (hS : LocallyFlatTopologicalSphere S) :
    ∃ D : Set V3, IsCompact D ∧ frontier D = S ∧ S ⊆ D ∧
      ∃ H : X3 ≃ₜ X3,
        (∀ x, H x ∈ ((↑) : V3 → X3) '' sphere (0 : V3) 1 ↔
          x ∈ ((↑) : V3 → X3) '' S) ∧
        ∀ x, H x ∈ ((↑) : V3 → X3) '' closedBall (0 : V3) 1 ↔
          x ∈ ((↑) : V3 → X3) '' D := by
  obtain ⟨D, hD, hfront, hSD, U, V, hU, hV, hUV, hunion, hUD, hVD,
    q, hq, hfib, hAU, hBV, hmark, hregion, p, _, hpa, hpb⟩ := hS.exists_end_quotient
  let J : X3 ≃ₜ S3 := onePointEquivSphereOfFinrankEq (by simp)
  let : CompactSpace S3 :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)
  let q' : C(S3, X3) := ⟨q ∘ J.symm, q.continuous.comp J.symm.continuous⟩
  have hq' : Function.Surjective q' := hq.comp J.symm.surjective
  have hfib' (x y : S3) : q' x = q' y ↔ x = y ∨
      (q' x = ((0 : V3) : X3) ∧ q' y = ((0 : V3) : X3)) ∨
      (q' x = ∞ ∧ q' y = ∞) :=
    (hfib (J.symm x) (J.symm y)).trans (or_congr J.symm.injective.eq_iff Iff.rfl)
  have hpa' : q' (J p) ≠ ((0 : V3) : X3) := by
    change q (J.symm (J p)) ≠ ((0 : V3) : X3)
    simpa only [J.symm_apply_apply] using hpa
  have hpb' : q' (J p) ≠ ∞ := by
    change q (J.symm (J p)) ≠ ∞
    simpa only [J.symm_apply_apply] using hpb
  have hUV' : Disjoint (J.symm ⁻¹' U) (J.symm ⁻¹' V) :=
    Set.disjoint_left.mpr fun _ hx hy => Set.disjoint_left.mp hUV hx hy
  have hAU' : q' ⁻¹' {((0 : V3) : X3)} ⊆ J.symm ⁻¹' U := fun _ hx => hAU hx
  have hBV' : q' ⁻¹' {∞} ⊆ J.symm ⁻¹' V := fun _ hx => hBV hx
  have hUD' : J.symm ⁻¹' U ⊆ J.symm ⁻¹' (((↑) : V3 → X3) '' D) := fun _ hx => hUD hx
  have hVD' : J.symm ⁻¹' V ⊆ (J.symm ⁻¹' (((↑) : V3 → X3) '' D))ᶜ :=
    fun _ hx => hVD.subset hx
  have hP' : J.symm ⁻¹' (((↑) : V3 → X3) '' S) ⊆
      ((J.symm ⁻¹' U) ∪ (J.symm ⁻¹' V))ᶜ := by
    intro x hx hside
    exact hunion.subset hside hx
  have hmark' (x : S3) : q' x ∈ ((↑) : V3 → X3) '' sphere (0 : V3) 1 ↔
      x ∈ J.symm ⁻¹' (((↑) : V3 → X3) '' S) := hmark (J.symm x)
  have hregion' (x : S3) : q' x ∈ ((↑) : V3 → X3) '' closedBall (0 : V3) 1 ↔
      x ∈ J.symm ⁻¹' (((↑) : V3 → X3) '' D) := hregion (J.symm x)
  obtain ⟨F, _, hFmark, hFregion⟩ := q'.exists_region_marked_sphere_quotient_cancellation
    hq' ((0 : V3) : X3) ∞ (OnePoint.coe_ne_infty (0 : V3)) hfib' (Homeomorph.refl S3) J
    (J p) hpa' hpb' (hU.preimage J.symm.continuous) (hV.preimage J.symm.continuous)
    hUV' hAU' hBV' hUD' hVD' hP' hmark' hregion'
  refine ⟨D, hD, hfront, hSD, J.trans F, ?_, ?_⟩
  · intro x
    have h := hFmark (J x)
    change F (J x) ∈ ((↑) : V3 → X3) '' sphere (0 : V3) 1 ↔ _
    simpa only [mem_preimage, J.symm_apply_apply] using h
  · intro x
    have h := hFregion (J x)
    change F (J x) ∈ ((↑) : V3 → X3) '' closedBall (0 : V3) 1 ↔ _
    simpa only [mem_preimage, J.symm_apply_apply] using h

end PoincareConjecture.M76.LocallyFlatTopologicalSphere
