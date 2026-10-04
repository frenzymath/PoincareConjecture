import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.BoundedRegionIncidence

/-!
# The exact exterior attachment in nested Alexander regions

Containment of the bounded open regions changes the choice
of complementary side. The bounded closed region and the
other complementary closed region meet exactly in the cap.
See Alexander 1924, p. 7 and M76 derivation 247.
-/

set_option autoImplicit false

open Set

namespace Set

/-- Nested open regions have exact cap overlap with the
opposite complementary closed region. This statement is
topological and applies also to relative regions in spherical
space. See Alexander p. 7 and M76 derivation 247. -/
theorem closure_inter_compl_eq_frontier_inter_of_subset {X : Type*}
    [TopologicalSpace X] {U V : Set X} (hV : IsOpen V)
    (hUV : U ⊆ V) : closure U ∩ Vᶜ = frontier U ∩ frontier V := by
  apply Subset.antisymm
  · intro x hx
    refine ⟨⟨hx.1, fun hi => hx.2 (hUV (interior_subset hi))⟩,
      ⟨(closure_mono hUV) hx.1, fun hi => hx.2 (interior_subset hi)⟩⟩
  · intro x hx
    refine ⟨hx.1.1, ?_⟩
    intro hxV
    exact hx.2.2 (by rwa [hV.interior_eq])

/-- A nested pair of capped regions meets exactly in the cap
when the outer region is replaced by its complementary closed
side. No compactness is asserted for an Euclidean exterior.
See Alexander p. 7 and M76 derivation 247. -/
theorem alexander_nested_region_inter_exterior {X : Type*} [TopologicalSpace X]
    {U V b c d q : Set X} (hV : IsOpen V)
    (hUV : U ⊆ V) (hUf : frontier U = b ∪ d) (hVf : frontier V = c ∪ d)
    (hbc : b ∩ c = q) (hqd : q ⊆ d) : closure U ∩ Vᶜ = d := by
  rw [closure_inter_compl_eq_frontier_inter_of_subset hV hUV, hUf, hVf]
  apply Subset.antisymm
  · intro x hx
    rcases hx.1 with hxb | hxd
    · rcases hx.2 with hxc | hxd
      · exact hqd (hbc ▸ And.intro hxb hxc)
      · exact hxd
    · exact hxd
  · intro x hx
    exact ⟨Or.inr hx, Or.inr hx⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Each capped-region configuration has an exact attachment
intersection: either both bounded closures meet in the cap,
or the bounded closure of the inner region meets the other's
complementary closed side there. The containment alternatives
are derived from the planar cap. See Alexander p. 7 and
M76 derivation 247. -/
theorem alexander_region_attachment_incidence {b c d q U V : Set E}
    (hb : IsFinitePLBallPair (ℝ × ℝ) b q)
    (hc : IsFinitePLBallPair (ℝ × ℝ) c q)
    (hbc : b ∩ c = q) (hbd : b ∩ d = q) (hcd : c ∩ d = q)
    (A : E →ᵃ[ℝ] ℝ) (v : E) (hv : 0 < A.linear v) {a : ℝ}
    (hdplane : d ⊆ {x | A x = a})
    (hU : IsOpen U) (hV : IsOpen V)
    (hUb : Bornology.IsBounded U) (hVb : Bornology.IsBounded V)
    (hUc : IsConnected U) (hVc : IsConnected V)
    (hUf : frontier U = b ∪ d) (hVf : frontier V = c ∪ d) :
    closure U ∩ closure V = d ∨
      (U ⊆ V ∧ closure U ∩ Vᶜ = d) ∨
      (V ⊆ U ∧ Uᶜ ∩ closure V = d) := by
  have hqd : q ⊆ d := by rw [← hbd]; exact inter_subset_right
  rcases alexander_bounded_region_incidence_open hb hc hbc hbd hcd A v hv hdplane
    hU hV hUb hVb hUc hVc hUf hVf with hinter | hUV | hVU
  · exact Or.inl hinter
  · exact Or.inr (Or.inl ⟨hUV,
      alexander_nested_region_inter_exterior hV hUV hUf hVf hbc hqd⟩)
  · right
    right
    refine ⟨hVU, ?_⟩
    rw [inter_comm]
    exact alexander_nested_region_inter_exterior hU hVU hVf hUf
      ((inter_comm _ _).trans hbc) hqd

end Set
