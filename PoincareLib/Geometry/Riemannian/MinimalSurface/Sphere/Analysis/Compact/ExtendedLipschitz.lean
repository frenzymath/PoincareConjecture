import Mathlib.Topology.Algebra.MetricSpace.Lipschitz

/-!
# Compact local Lipschitz bounds in an extended metric

Morgan-Tian Definition 18.17, printed p. 430, boundary regularization.
On a compact source, local Lipschitz bounds give a global bound provided
all pairs in the image have finite extended distance. The finite-distance
condition is retained for disconnected Riemannian targets.
-/

set_option autoImplicit false

open Set
open scoped Topology NNReal

namespace PoincareMT.M60

/-- A compact local Lipschitz bound globalizes in an extended metric
when the image lies in one finite-distance component. Source: MT
Definition 18.17, p. 430, annular regularity derivation. -/
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

end PoincareMT.M60
