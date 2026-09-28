import Mathlib.Topology.CompactOpen










set_option autoImplicit false

open Set

namespace PoincareConjecture.M14

variable {P K F : Type*} [TopologicalSpace P] [TopologicalSpace K] [TopologicalSpace F]




theorem exists_continuousOn_pathFamily {U : Set P} (f : P × K → F)
    (hf : ContinuousOn f (U ×ˢ univ)) (fallback : C(K, F)) :
    ∃ Φ : P → C(K, F), ContinuousOn Φ U ∧ ∀ p ∈ U, ∀ k, Φ p k = f (p, k) := by
  classical
  let Φ : P → C(K, F) := fun p => if hp : p ∈ U then
    ⟨fun k => f (p, k), hf.comp_continuous (continuous_const.prodMk continuous_id)
      (fun _ => ⟨hp, mem_univ _⟩)⟩ else fallback
  have heq (p : P) (hp : p ∈ U) (k : K) : Φ p k = f (p, k) := by
    simp only [Φ, dif_pos hp, ContinuousMap.coe_mk]
  refine ⟨Φ, ContinuousMap.continuousOn_of_continuousOn_uncurry Φ ?_, heq⟩
  exact hf.congr (fun z hz => heq z.1 hz.1 z.2)

end PoincareConjecture.M14
