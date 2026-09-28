import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Nested.Caps.Components
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Sublevel.Minimum

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Nested

private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

private theorem exists_critical_in_open_sublevel
    {h : S2 → Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    {U : Set S2} (hU : IsOpen U) (hne : U.Nonempty) {c : Real}
    (hbelow : ∀ p ∈ U, h p<c) (hfront : ∀ p ∈ frontier U, h p=c) :
    ∃ p ∈ U, mfderiv (𝓡 2) 𝓘(Real, Real) h p=0 := by
  obtain ⟨q, hq⟩ := hne
  obtain ⟨p, hp, hmin⟩ := isClosed_closure.isCompact.exists_isMinOn
    ⟨q, subset_closure hq⟩ hh.continuous.continuousOn
  have hlt : h p<c := (hmin (subset_closure hq)).trans_lt (hbelow q hq)
  have hpU : p ∈ U := by
    by_contra hout
    have hpf : p ∈ frontier U := by
      rw [hU.frontier_eq]
      exact ⟨hp, hout⟩
    exact (ne_of_lt hlt) (hfront p hpf)
  refine ⟨p, hpU, Poincare.Geometry.Manifold.mfderiv_eq_zero_of_isLocalMin hh ?_⟩
  exact hmin.isLocalMin (Filter.mem_of_superset (hU.mem_nhds hpU) subset_closure)

theorem exists_critical_in_capRegion (i : Fin 3) :
    ∃ p ∈ capRegion i, mfderiv (𝓡 2) 𝓘(Real, Real) height p=0 := by
  have houter : outerSourceCircle ⊆ height ⁻¹' {(1 : Real)} := by
    rw [lower_height_level_eq_sourceCircles]
    exact subset_union_left
  have hinner : innerSourceCircle ⊆ height ⁻¹' {(1 : Real)} := by
    rw [lower_height_level_eq_sourceCircles]
    exact subset_union_right
  fin_cases i
  · exact exists_critical_in_open_sublevel height_contMDiff isOpen_southernCap
      southernCap_nonempty (fun p hp => hp.1) (fun p hp => houter (frontier_southernCap_subset hp))
  · exact exists_critical_in_open_sublevel height_contMDiff isOpen_northernCap
      northernCap_nonempty (fun p hp => hp.1) (fun p hp => hinner (frontier_northernCap_subset hp))
  · obtain ⟨p, hp, hc⟩ := exists_critical_in_open_sublevel height_contMDiff.neg isOpen_upperCap
      upperCap_nonempty (c := -(13/10))
      (fun p hp => neg_lt_neg (show 13/10 < height p from hp))
      (fun p hp => congrArg Neg.neg (show height p=13/10 from frontier_upperCap_subset hp))
    refine ⟨p, hp, ?_⟩
    change mfderiv (𝓡 2) 𝓘(Real, Real) (-height) p=0 at hc
    simpa only [mfderiv_neg, neg_eq_zero] using hc

end Poincare.Manifold.Schoenflies.Saddle.Nested
