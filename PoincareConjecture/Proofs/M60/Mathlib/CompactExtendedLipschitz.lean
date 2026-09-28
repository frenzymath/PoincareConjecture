import Mathlib.Topology.Algebra.MetricSpace.Lipschitz










set_option autoImplicit false

open Set
open scoped Topology NNReal

namespace PoincareConjecture.M60




theorem exists_lipschitzOnWith_of_compact_edist_ne_top
    {X Y : Type*} [PseudoMetricSpace X] [PseudoEMetricSpace Y]
    {S : Set X} (hS : IsCompact S) {f : X → Y} (hf : LocallyLipschitzOn S f)
    (hfinite : ∀ x ∈ S, ∀ y ∈ S, edist (f x) (f y) ≠ ⊤) :
    ∃ K : ℝ≥0, LipschitzOnWith K f S := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let R := f '' S
  have hR (x y : R) : edist x y ≠ ⊤ := by
    obtain ⟨a, ha, hea⟩ := x.property
    obtain ⟨b, hb, heb⟩ := y.property
    change edist x.val y.val ≠ ⊤
    rw [← hea, ← heb]
    exact hfinite a ha b hb
  let : PseudoMetricSpace R := PseudoEMetricSpace.toPseudoMetricSpace hR
  let F : S → R := fun x => ⟨f x.val, mem_image_of_mem f x.property⟩
  have hF : LocallyLipschitz F := by
    intro x
    obtain ⟨K, U, hU, hLip⟩ := hf.restrict x
    exact ⟨K, U, hU, fun a ha b hb => hLip ha hb⟩
  obtain ⟨K, hK⟩ := hF.locallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_univ : IsCompact (univ : Set S))
  exact ⟨K, fun x hx y hy => hK (mem_univ (⟨x, hx⟩ : S)) (mem_univ (⟨y, hy⟩ : S))⟩

end PoincareConjecture.M60
