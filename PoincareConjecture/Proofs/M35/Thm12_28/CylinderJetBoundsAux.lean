import PoincareConjecture.Proofs.M35.Thm12_28.CylinderFrechetJets
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.LinearAlgebra.Multilinear.Basis
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional

set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology BigOperators

namespace PoincareConjecture.M35

theorem exists_cylinder_component_norm_bound (r : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ T : RoundCylinderCoordinates [×r]→L[ℝ] ℝ,
      ∀ C : ℝ, 0 ≤ C →
      (∀ a : Fin r → Fin 3, |T (fun j => roundCylinderCoordinateBasis (a j))| ≤ C) →
      ‖T‖ ≤ K * C := by
  let ev : (RoundCylinderCoordinates [×r]→L[ℝ] ℝ) →ₗ[ℝ] ((Fin r → Fin 3) → ℝ) :=
    { toFun := fun T a => T (fun j => roundCylinderCoordinateBasis (a j))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let b := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.map cylinderCoordinateEquiv.toLinearEquiv
  have hb (i : Fin 3) : b i = roundCylinderCoordinateBasis i :=
    cylinderCoordinateEquiv_basis i
  have hinj : Function.Injective ev := by
    intro T S hTS
    apply ContinuousMultilinearMap.toMultilinearMap_injective
    apply Module.Basis.ext_multilinear (fun _ => b)
    intro a
    change T (fun j => b (a j)) = S (fun j => b (a j))
    simp only [hb]
    exact congrFun hTS a
  let : FiniteDimensional ℝ (RoundCylinderCoordinates [×r]→L[ℝ] ℝ) :=
    FiniteDimensional.of_injective ev hinj
  obtain ⟨K, hK, hanti⟩ := ev.injective_iff_antilipschitz.mp hinj
  refine ⟨K, hK, ?_⟩
  intro T C hC hcomponents
  have hnorm : ‖ev T‖ ≤ C := (pi_norm_le_iff_of_nonneg hC).mpr hcomponents
  exact (hanti.le_mul_norm (map_zero ev) T).trans
    (mul_le_mul_of_nonneg_left hnorm K.coe_nonneg)

theorem norm_iteratedFDeriv_mul_le_at
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f g : V → ℝ} {p : V} (r : ℕ)
    (hf : ContDiffAt ℝ ∞ f p) (hg : ContDiffAt ℝ ∞ g p) :
    ‖iteratedFDeriv ℝ r (fun y => f y * g y) p‖ ≤
      ∑ j ∈ Finset.range (r + 1), (r.choose j : ℝ) *
        ‖iteratedFDeriv ℝ j f p‖ * ‖iteratedFDeriv ℝ (r - j) g p‖ := by
  have hr : (r : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top (a := (r : ℕ∞))
  obtain ⟨Sf, hSf, hfs⟩ := hf.contDiffOn (m := r) hr (by simp)
  obtain ⟨Sg, hSg, hgs⟩ := hg.contDiffOn (m := r) hr (by simp)
  obtain ⟨U, hUsub, hU, hpU⟩ := mem_nhds_iff.mp (inter_mem hSf hSg)
  have h := norm_iteratedFDerivWithin_mul_le
    (hfs.mono (hUsub.trans inter_subset_left))
    (hgs.mono (hUsub.trans inter_subset_right)) hU.uniqueDiffOn hpU (le_refl (r : ℕ∞ω))
  simpa only [iteratedFDerivWithin_of_isOpen _ hU hpU] using h

theorem iteratedFDeriv_directional_apply
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : V → ℝ} {p : V} (r : ℕ) (hf : ContDiffAt ℝ ∞ f p)
    (v : Fin (r + 1) → V) :
    iteratedFDeriv ℝ (r + 1) f p v =
      iteratedFDeriv ℝ r (fun y => fderiv ℝ f y (v (Fin.last r))) p (Fin.init v) := by
  rw [iteratedFDeriv_succ_apply_right]
  let L := ContinuousLinearMap.apply ℝ ℝ (v (Fin.last r))
  have heq := L.iteratedFDeriv_comp_left (hf.fderiv_right (by simp))
    (show (r : ℕ∞ω) ≤ ∞ by exact_mod_cast le_top (a := (r : ℕ∞)))
  exact (congrArg (fun T : V [×r]→L[ℝ] ℝ => T (Fin.init v)) heq).symm

end PoincareConjecture.M35
