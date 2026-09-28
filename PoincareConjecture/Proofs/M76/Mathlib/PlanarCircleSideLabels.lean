import PoincareConjecture.Proofs.M76.Mathlib.PlanarRegionSideTransport
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLCirclePoleBranches

set_option autoImplicit false

open Set

namespace Set

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nonempty ι]

theorem IsFinitePLBallPair.exists_common_planar_circle_side_labels
    {d q : Set E} (hd : IsFinitePLBallPair (ℝ × ℝ) d q)
    (A : E →ᵃ[ℝ] ℝ) (hA : A.linear ≠ 0) (hdim : Module.finrank ℝ E = 3)
    (hdplane : d ⊆ {x | A x = 0}) (arc : Bool → Set E) {a b : E}
    (hArc : ∀ i, IsFinitePLBallPair ℝ (arc i) {a, b})
    (hArcPlane : ∀ i, arc i ⊆ {x | A x = 0})
    (hcontact : ∀ i, arc i ∩ q ⊆ {a, b})
    (positive negative : ι → Set E)
    (hlabels : ∀ j, ∃ i : Bool, positive j ⊆ arc i ∧ negative j ⊆ arc (!i))
    (hpositive : ∀ j, ∃ x ∈ positive j, x ∉ ({a, b} : Set E) ∧ x ∈ d)
    (hnegative : ∀ j, ∃ x ∈ negative j, x ∉ ({a, b} : Set E) ∧ x ∉ d) :
    ∃ i : Bool, arc i \ {a, b} ⊆ d ∧ arc (!i) \ {a, b} ⊆ dᶜ ∧
      ∀ j, positive j ⊆ arc i ∧ negative j ⊆ arc (!i) := by
  have hconstant (i : Bool) {x y : E}
      (hx : x ∈ arc i \ {a, b}) (hy : y ∈ arc i \ {a, b}) : x ∈ d ↔ y ∈ d := by
    apply hd.mem_iff_of_preconnected_avoiding_rim_in_plane A hA hdim hdplane
      (hArc i).isConnected_sdiff.isPreconnected (sdiff_subset.trans (hArcPlane i))
      (disjoint_left.mpr fun z hz hzq => hz.2 (hcontact i ⟨hz.1, hzq⟩)) hx hy
  obtain ⟨j₀⟩ := ‹Nonempty ι›
  obtain ⟨i, hpi, hni⟩ := hlabels j₀
  obtain ⟨x, hxp, hxmarks, hxd⟩ := hpositive j₀
  obtain ⟨y, hyn, hymarks, hyd⟩ := hnegative j₀
  have hinside : arc i \ {a, b} ⊆ d := fun z hz =>
    (hconstant i ⟨hpi hxp, hxmarks⟩ hz).mp hxd
  have houtside : arc (!i) \ {a, b} ⊆ dᶜ := by
    intro z hz hzd
    exact hyd ((hconstant (!i) hz ⟨hni hyn, hymarks⟩).mp hzd)
  refine ⟨i, hinside, houtside, ?_⟩
  intro j
  obtain ⟨k, hpk, hnk⟩ := hlabels j
  have hki : k = i := by
    by_contra hne
    have hk : k = !i := by
      cases i <;> cases k
      · exact (hne rfl).elim
      · rfl
      · rfl
      · exact (hne rfl).elim
    obtain ⟨z, hzp, hzmarks, hzd⟩ := hpositive j
    exact houtside ⟨hk ▸ hpk hzp, hzmarks⟩ hzd
  subst k
  exact ⟨hpk, hnk⟩

end Set
