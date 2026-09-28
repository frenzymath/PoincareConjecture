import PoincareConjecture.Proofs.M76.Brown.LocallyFlatCompactifiedBicollar
import PoincareConjecture.Proofs.M76.Brown.ClosedCylinderQuotientRegions

set_option autoImplicit false

open Set Metric
open scoped OnePoint

namespace PoincareConjecture.M76.LocallyFlatTopologicalSphere

local notation "V3" => (Fin 3 → ℝ)
local notation "X3" => OnePoint V3

theorem exists_end_quotient {S : Set V3} (hS : LocallyFlatTopologicalSphere S) :
    ∃ D : Set V3, IsCompact D ∧ frontier D = S ∧ S ⊆ D ∧
      ∃ U V : Set X3, IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧
        U ∪ V = (((↑) : V3 → X3) '' S)ᶜ ∧
        U ⊆ ((↑) : V3 → X3) '' D ∧ V = (((↑) : V3 → X3) '' D)ᶜ ∧
        ∃ q : C(X3, X3), Function.Surjective q ∧
          (∀ x y, q x = q y ↔ x = y ∨
            (q x = ((0 : V3) : X3) ∧ q y = ((0 : V3) : X3)) ∨
            (q x = ∞ ∧ q y = ∞)) ∧
          q ⁻¹' {((0 : V3) : X3)} ⊆ U ∧ q ⁻¹' {∞} ⊆ V ∧
          (∀ x, q x ∈ ((↑) : V3 → X3) '' sphere (0 : V3) 1 ↔
            x ∈ ((↑) : V3 → X3) '' S) ∧
          (∀ x, q x ∈ ((↑) : V3 → X3) '' closedBall (0 : V3) 1 ↔
            x ∈ ((↑) : V3 → X3) '' D) ∧
          ∃ p : X3, p ∈ ((↑) : V3 → X3) '' S ∧
            q p ≠ ((0 : V3) : X3) ∧ q p ≠ ∞ := by
  obtain ⟨D, hD, hfront, hSD, U, V, hU, hV, hUV, hunion, hUD, hVD,
    e, hes, hbase, hneg, hpos, hheight⟩ := hS.exists_compactified_bicollar
  have hT : (sphere (0 : V3) 1).Nonempty := NormedSpace.sphere_nonempty.mpr zero_le_one
  let : Nonempty (sphere (0 : V3) 1) := hT.to_subtype
  have hunion' : U ∪ V = (BrownSchoenflies.bicollarBaseImage e)ᶜ := by
    rw [hbase]
    exact hunion
  obtain ⟨A, B, hA, hB, hAB, hAU, hBV, _, _, hcover, hAend, hBend⟩ :=
    BrownSchoenflies.exists_closed_bicollar_ends e hes hU hV hUV hunion' hneg hpos
  obtain ⟨q, hq, hqA, hqB, hqC⟩ :=
    BrownSchoenflies.exists_closed_cylinder_quotient e hes hA hB hAB hcover hAend hBend
  obtain ⟨hzero, hinfty, hfib⟩ :=
    BrownSchoenflies.closed_cylinder_quotient_fibers e hes hcover hAend hBend q hqA hqB hqC
  have hBD : B ⊆ (((↑) : V3 → X3) '' D)ᶜ := by
    rw [← hVD]
    exact hBV
  obtain ⟨hmark, hball⟩ := BrownSchoenflies.closed_cylinder_quotient_regions e hes
    hcover hAend hBend (hAU.trans hUD) hBD hheight q hqA hqB hqC
  have hmark' (x : X3) : q x ∈ ((↑) : V3 → X3) '' sphere (0 : V3) 1 ↔
      x ∈ ((↑) : V3 → X3) '' S := by
    simpa only [hbase] using hmark x
  refine ⟨D, hD, hfront, hSD, U, V, hU, hV, hUV, hunion, hUD, hVD,
    q, hq, ?_, ?_, ?_, hmark', hball, ?_⟩
  · intro x y
    rw [hzero x, hzero y, hinfty x, hinfty y]
    exact hfib x y
  · intro x hx
    exact hAU ((hzero x).mp hx)
  · intro x hx
    exact hBV ((hinfty x).mp hx)
  · obtain ⟨u, hu⟩ := hT
    let s : S := hS.parametrization ⟨u, hu⟩
    let p : X3 := (s : V3)
    have hp : p ∈ ((↑) : V3 → X3) '' S := ⟨s, s.property, rfl⟩
    have hqp := (hmark' p).mpr hp
    refine ⟨p, hp, ?_, ?_⟩
    · intro heq
      rw [heq, OnePoint.coe_injective.mem_set_image, mem_sphere_zero_iff_norm,
        norm_zero] at hqp
      exact zero_ne_one hqp
    · intro heq
      rw [heq] at hqp
      exact OnePoint.infty_notMem_image_coe hqp

end PoincareConjecture.M76.LocallyFlatTopologicalSphere
