import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Resolution.Strips.Coordinates
import PoincareConjecture.Proofs.Horizon.Topology.Connected.BoundaryIncidence

noncomputable section
set_option autoImplicit false

open Set Metric
open scoped Topology

namespace Poincare.Manifold.Schoenflies.SaddleLevel

theorem strip_slice_exterior_iff {M : Type*} [TopologicalSpace M]
    {U : Set M} (hU : IsOpen U) {a A m B b : Real}
    (haA : a < A) (hAm : A < m) (hmB : m < B) (hBb : B < b)
    {γ : Real → M} (hγ : ContinuousOn γ (Icc a b))
    (ha : γ a ∈ U) (hb : γ b ∈ U) (hm : γ m ∉ closure U)
    (hA : γ A ∉ U) (hB : γ B ∉ U)
    (hboundary : ∀ s ∈ Icc a b, γ s ∈ frontier U → s = A ∨ s = B)
    {s : Real} (hs : s ∈ Icc a b) :
    γ s ∉ U ↔ s ∈ Icc A B := by
  have hAB : A < B := hAm.trans hmB
  have hleft : γ '' Ico a A ⊆ U := by
    have hsub : Ico a A ⊆ Icc a b :=
      fun x hx => ⟨hx.1, hx.2.le.trans (hAB.trans hBb).le⟩
    have hc : IsPreconnected (γ '' Ico a A) :=
      isPreconnected_Ico.image γ (hγ.mono hsub)
    have hd : Disjoint (γ '' Ico a A) (frontier U) := by
      apply disjoint_left.mpr
      rintro x ⟨u, hu, rfl⟩ hx
      rcases hboundary u (hsub hu) hx with he | he <;> subst u <;> linarith [hu.2]
    have hm' : (γ '' Ico a A ∩ interior U).Nonempty :=
      ⟨γ a, ⟨a, ⟨le_rfl, haA⟩, rfl⟩, hU.interior_eq.symm ▸ ha⟩
    exact (Poincare.Topology.preconnected_subset_interior_of_disjoint_frontier hc hd hm').trans
      interior_subset
  have hright : γ '' Ioc B b ⊆ U := by
    have hsub : Ioc B b ⊆ Icc a b :=
      fun x hx => ⟨(haA.trans hAB).le.trans hx.1.le, hx.2⟩
    have hc : IsPreconnected (γ '' Ioc B b) :=
      isPreconnected_Ioc.image γ (hγ.mono hsub)
    have hd : Disjoint (γ '' Ioc B b) (frontier U) := by
      apply disjoint_left.mpr
      rintro x ⟨u, hu, rfl⟩ hx
      rcases hboundary u (hsub hu) hx with he | he <;> subst u <;> linarith [hu.1]
    have hm' : (γ '' Ioc B b ∩ interior U).Nonempty :=
      ⟨γ b, ⟨b, ⟨hBb, le_rfl⟩, rfl⟩, hU.interior_eq.symm ▸ hb⟩
    exact (Poincare.Topology.preconnected_subset_interior_of_disjoint_frontier hc hd hm').trans
      interior_subset
  have hmiddle : γ '' Ioo A B ⊆ Uᶜ := by
    have hsub : Ioo A B ⊆ Icc a b :=
      fun x hx => ⟨haA.le.trans hx.1.le, hx.2.le.trans hBb.le⟩
    have hc : IsPreconnected (γ '' Ioo A B) :=
      isPreconnected_Ioo.image γ (hγ.mono hsub)
    have hd : Disjoint (γ '' Ioo A B) (frontier Uᶜ) := by
      rw [frontier_compl]
      apply disjoint_left.mpr
      rintro x ⟨u, hu, rfl⟩ hx
      rcases hboundary u (hsub hu) hx with he | he <;> subst u <;> linarith [hu.1, hu.2]
    have hm' : (γ '' Ioo A B ∩ interior Uᶜ).Nonempty := by
      refine ⟨γ m, ⟨m, ⟨hAm, hmB⟩, rfl⟩, ?_⟩
      rwa [interior_compl]
    exact (Poincare.Topology.preconnected_subset_interior_of_disjoint_frontier hc hd hm').trans
      interior_subset
  constructor
  · intro hout
    constructor
    · by_contra hnot
      exact hout (hleft ⟨s, ⟨hs.1, lt_of_not_ge hnot⟩, rfl⟩)
    · by_contra hnot
      exact hout (hright ⟨s, ⟨lt_of_not_ge hnot, hs.2⟩, rfl⟩)
  · intro hmid
    rcases eq_or_lt_of_le hmid.1 with he | he
    · exact he ▸ hA
    rcases eq_or_lt_of_le hmid.2 with he' | he'
    · exact he' ▸ hB
    exact hmiddle ⟨s, ⟨he, he'⟩, rfl⟩

end Poincare.Manifold.Schoenflies.SaddleLevel
