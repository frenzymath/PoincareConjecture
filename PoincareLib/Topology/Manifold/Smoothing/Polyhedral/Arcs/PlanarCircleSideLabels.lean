import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.PlanarRegionSideTransport
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Arcs.FinitePLCirclePoleBranches

/-!
# One inside label for all original planar circle branches

Connected complements of the two original marked arcs cannot
cross the actual planar filling rim. Opposite local branches
with genuine inside and outside witnesses therefore have
one common global labeling. See Alexander 1924, pp. 6--8,
Hudson 1969, pp. 15--19 and M76 derivation 286ad.
-/

set_option autoImplicit false

open Set

namespace Set

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nonempty ι]

/-- The same actual planar disk labels every complete local
branch consistently. Only one off-mark inside and outside
witness is needed per branch pair; complete branch inclusion
then follows from the original opposite-arc certificates.
See Alexander pp. 6--8 and M76 derivation 286ad. -/
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
