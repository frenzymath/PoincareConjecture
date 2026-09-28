import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Sqrt









set_option autoImplicit false

open Set Filter
open scoped Topology

namespace PoincareConjecture.M10


theorem homogeneous_ray_eq {f : ℝ → ℝ} {b C : ℝ} (hb : 0 < b)
    (hf : ∀ t ∈ Ioo 0 b, HasDerivAt f (f t / t) t)
    (hlim : Tendsto (fun s : ℝ ↦ (s⁻¹) ^ 2 * f (s ^ 2))
      (𝓝[>] (0 : ℝ)) (𝓝 C)) {t : ℝ} (ht : t ∈ Ioo 0 b) :
    f t = C * t := by
  have hd (r : ℝ) (hr : r ∈ Ioo 0 b) : HasDerivAt (fun s ↦ f s / s) 0 r := by
    apply ((hf r hr).div (hasDerivAt_id r) hr.1.ne').congr_deriv
    simp only [id_eq]
    field_simp [hr.1.ne']
    ring
  have hconst (r : ℝ) (hr : r ∈ Ioo 0 b) : f r / r = f t / t :=
    isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo 0 b).isPreconnected
      (fun s hs ↦ (hd s hs).differentiableAt.differentiableWithinAt)
      (fun s hs ↦ (hd s hs).deriv) hr ht
  have heq : (fun s : ℝ ↦ (s⁻¹) ^ 2 * f (s ^ 2)) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun _ ↦ f t / t) := by
    filter_upwards [Ioo_mem_nhdsGT (Real.sqrt_pos.2 hb)] with s hs
    have hsquare : s ^ 2 ∈ Ioo 0 b := by
      refine ⟨sq_pos_of_pos hs.1, ?_⟩
      nlinarith [Real.sq_sqrt hb.le, hs.1, hs.2]
    calc
      (s⁻¹) ^ 2 * f (s ^ 2) = f (s ^ 2) / s ^ 2 := by
        rw [div_eq_mul_inv, inv_pow]
        ring
      _ = f t / t := hconst (s ^ 2) hsquare
  have hC : C = f t / t := tendsto_nhds_unique (hlim.congr' heq) tendsto_const_nhds
  exact (div_eq_iff ht.1.ne').mp hC.symm

end PoincareConjecture.M10
