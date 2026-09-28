import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.FiniteDimensional.Basic











set_option autoImplicit false

namespace LinearMap




theorem exists_axis_of_not_injective_fst
    {K V E : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup E] [Module K E]
    (L : V →ₗ[K] E × K) (hL : Function.Injective L)
    (hP : ¬ Function.Injective (fun v => (L v).1)) :
    ∃ v : V, L v = (0, 1) := by
  obtain ⟨v, w, hvw, hne⟩ := Function.not_injective_iff.mp hP
  let a := v - w
  have ha : a ≠ 0 := sub_ne_zero.mpr hne
  have hfirst : (L a).1 = 0 := by
    change (L (v - w)).1 = 0
    simpa only [map_sub, Prod.fst_sub, sub_eq_zero] using hvw
  have hsecond : (L a).2 ≠ 0 := by
    intro hz
    apply ha
    apply hL
    rw [map_zero]
    exact Prod.ext hfirst hz
  refine ⟨(L a).2⁻¹ • a, ?_⟩
  rw [map_smul]
  exact Prod.ext (by simp only [Prod.smul_fst, hfirst, smul_zero])
    (by simp only [Prod.smul_snd, smul_eq_mul, inv_mul_cancel₀ hsecond])




theorem exists_horizontal_of_axis_mem_range
    {K V E : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup E] [Module K E]
    (L : V →ₗ[K] E × K) (hL : Function.Injective L)
    (hdim : 1 < Module.finrank K V) (haxis : (0, 1) ∈ LinearMap.range L) :
    ∃ u : E, u ≠ 0 ∧ (u, 0) ∈ LinearMap.range L := by
  have hnonzero : ∃ v : V, (L v).1 ≠ 0 := by
    by_contra! h
    have hinj : Function.Injective ((LinearMap.snd K E K).comp L) := by
      intro v w hvw
      apply hL
      exact Prod.ext (by rw [h v, h w]) hvw
    have hd := LinearMap.finrank_le_finrank_of_injective hinj
    simp only [Module.finrank_self] at hd
    exact (not_le_of_gt hdim) hd
  obtain ⟨v, hv⟩ := hnonzero
  refine ⟨(L v).1, hv, ?_⟩
  have hm := (LinearMap.range L).sub_mem (LinearMap.mem_range_self L v)
    ((LinearMap.range L).smul_mem (L v).2 haxis)
  convert hm using 1
  ext <;> simp

end LinearMap
