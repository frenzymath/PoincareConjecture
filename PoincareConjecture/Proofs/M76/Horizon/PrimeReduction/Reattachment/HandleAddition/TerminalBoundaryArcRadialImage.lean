import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.TerminalBoundaryArcEnd
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Mathlib.CircleInjectivity
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOneSquareCircle

set_option autoImplicit false
open Set Metric
namespace PoincareConjecture.M76

theorem range_eq_sphere_of_injective_circle
    {κ : Type*} [Fintype κ] (hk : Fintype.card κ = 2)
    {r : ℝ} (hr : 0 < r)
    (v : C(sphere (0 : Fin 2 → ℝ) 1,κ → ℝ))
    (hi : Function.Injective v) (hn : ∀ y, ‖v y‖ = r) :
    range v = sphere (0 : κ → ℝ) r := by
  let e : (Fin 2 → ℝ) ≃L[ℝ] (κ → ℝ) := ContinuousLinearEquiv.ofFinrankEq (by simp [hk])
  let H := PoincareConjecture.Proofs.M02.Topology.unitSphereHomeomorph e
  let w : C(sphere (0 : Fin 2 → ℝ) 1,sphere (0 : κ → ℝ) 1) :=
    ⟨fun y => ⟨r⁻¹ • v y,by
      rw [mem_sphere_zero_iff_norm,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hr,hn]
      exact inv_mul_cancel₀ hr.ne'⟩,
      by fun_prop⟩
  have hwi : Function.Injective w := by
    intro x y h
    apply hi
    exact (smul_right_injective (κ → ℝ) (inv_ne_zero hr.ne')) (congrArg Subtype.val h)
  let C := HamiltonIndexOne.squareCircle
  let f := C.symm ∘ H.symm ∘ w ∘ C
  have hfc : Continuous f := C.symm.continuous.comp
    (H.symm.continuous.comp (w.continuous.comp C.continuous))
  have hfi : Function.Injective f := C.symm.injective.comp
    (H.symm.injective.comp (hwi.comp C.injective))
  let : Fact (0 < 4 * (2 : ℝ)) := ⟨by norm_num⟩
  have hfs := AddCircle.surjective_of_continuous_injective hfc hfi
  apply Subset.antisymm
  · rintro _ ⟨y,rfl⟩
    exact mem_sphere_zero_iff_norm.mpr (hn y)
  · intro z hz
    let z' : sphere (0 : κ → ℝ) 1 := ⟨r⁻¹ • z,by
      rw [mem_sphere_zero_iff_norm,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hr,
        mem_sphere_zero_iff_norm.mp hz]
      exact inv_mul_cancel₀ hr.ne'⟩
    obtain ⟨y,hy⟩ := hfs (C.symm (H.symm z'))
    have hw : w (C y) = z' := H.symm.injective (C.symm.injective hy)
    refine ⟨C y,?_⟩
    exact (smul_right_injective (κ → ℝ) (inv_ne_zero hr.ne')) (congrArg Subtype.val hw)

theorem range_radial_half_collar
    {κ Y : Type*} [Fintype κ] [TopologicalSpace Y]
    {r : ℝ} (hr : 0 < r) (v : C(Y,κ → ℝ))
    (hv : range v = sphere (0 : κ → ℝ) r) :
    range (fun z : Y × Set.Icc (0 : ℝ) 1 => (1 - (z.2 : ℝ) / 2) • v z.1) =
      {x : κ → ℝ | r / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ r} := by
  have hn (y : Y) : ‖v y‖ = r := mem_sphere_zero_iff_norm.mp (hv ▸ mem_range_self y)
  apply Subset.antisymm
  · rintro _ ⟨⟨y,t⟩,rfl⟩
    change r / 2 ≤ ‖(1 - (t : ℝ) / 2) • v y‖ ∧ _
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by linarith [t.property.2]),hn]
    constructor <;> nlinarith [t.property.1,t.property.2]
  · intro x hx
    have hnpos : 0 < ‖x‖ := lt_of_lt_of_le (by linarith : 0 < r / 2) hx.1
    have hxrim : (r / ‖x‖) • x ∈ sphere (0 : κ → ℝ) r := by
      rw [mem_sphere_zero_iff_norm,norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos hr hnpos)]
      exact div_mul_cancel₀ r hnpos.ne'
    obtain ⟨y,hy⟩ := hv.symm ▸ hxrim
    let t : Set.Icc (0 : ℝ) 1 := ⟨2 - 2 * ‖x‖ / r,by
      constructor
      · have hh : 2 * ‖x‖ / r ≤ 2 := (div_le_iff₀ hr).mpr (by nlinarith [hx.2])
        linarith
      · have hh : 1 ≤ 2 * ‖x‖ / r := (le_div_iff₀ hr).mpr (by nlinarith [hx.1])
        linarith⟩
    refine ⟨(y,t),?_⟩
    change (1 - (2 - 2 * ‖x‖ / r) / 2) • v y = x
    rw [hy,smul_smul]
    have heq : (1 - (2 - 2 * ‖x‖ / r) / 2) * (r / ‖x‖) = 1 := by
      field_simp
      ring
    rw [heq,one_smul]

end PoincareConjecture.M76
