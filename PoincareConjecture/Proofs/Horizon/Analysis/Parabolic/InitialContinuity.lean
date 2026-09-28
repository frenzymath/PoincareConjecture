import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.UniformSpace.UniformApproximation









set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Poincare.Parabolic

variable {M E : Type*} [TopologicalSpace M] [UniformSpace E]



theorem tendsto_joint_initial_of_tendstoUniformly
    {F : ℝ × M → E} {f : M → E} {x : M}
    (hlim : TendstoUniformly (fun t y ↦ F (t, y)) f (𝓝[>] (0 : ℝ)))
    (hf : ContinuousAt f x) :
    Tendsto F ((𝓝[>] (0 : ℝ)) ×ˢ 𝓝 x) (𝓝 (f x)) := by
  have hprod : TendstoUniformly (fun p : ℝ × M ↦ fun y ↦ F (p.1, y)) f
      ((𝓝[>] (0 : ℝ)) ×ˢ 𝓝 x) := by
    intro u hu
    exact tendsto_fst.eventually (hlim u hu)
  exact hprod.tendsto_comp hf tendsto_snd



theorem continuousOn_nonneg_of_tendstoUniformly
    {F : ℝ × M → E} {f : M → E}
    (hF : ContinuousOn F (Ioi 0 ×ˢ univ))
    (hf : Continuous f)
    (hlim : TendstoUniformly (fun t y ↦ F (t, y)) f (𝓝[>] (0 : ℝ)))
    (hzero : ∀ x, F (0, x) = f x) :
    ContinuousOn F (Ici 0 ×ˢ univ) := by
  rintro ⟨t, x⟩ ht
  rcases eq_or_lt_of_le (mem_Ici.mp ht.1) with ht | ht
  · change 0 = t at ht
    subst t
    change Tendsto F (𝓝[Ici 0 ×ˢ univ] (0, x)) (𝓝 (F (0, x)))
    rw [hzero, nhdsWithin_prod_eq, nhdsWithin_univ, ← Ioi_insert,
      nhdsWithin_insert, sup_prod, tendsto_sup]
    constructor
    · rw [pure_prod, tendsto_map'_iff]
      simpa only [Function.comp_def, hzero] using hf.tendsto x
    · exact tendsto_joint_initial_of_tendstoUniformly hlim hf.continuousAt
  · exact (hF.continuousAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds
      ⟨ht, mem_univ x⟩)).continuousWithinAt



theorem continuousOn_initialExtension_of_tendstoUniformly
    {F : ℝ × M → E} {f : M → E}
    (hF : ContinuousOn F (Ioi 0 ×ˢ univ))
    (hf : Continuous f)
    (hlim : TendstoUniformly (fun t y ↦ F (t, y)) f (𝓝[>] (0 : ℝ))) :
    ContinuousOn (fun p : ℝ × M ↦ if p.1 = 0 then f p.2 else F p)
      (Ici 0 ×ˢ univ) := by
  apply continuousOn_nonneg_of_tendstoUniformly (f := f)
  · apply hF.congr
    intro p hp
    simp only [ne_of_gt (mem_Ioi.mp hp.1), if_false]
  · exact hf
  · intro u hu
    filter_upwards [hlim u hu, self_mem_nhdsWithin] with t ht hpos
    intro x
    simpa only [ne_of_gt (mem_Ioi.mp hpos), if_false] using ht x
  · intro x
    simp

end Poincare.Parabolic
