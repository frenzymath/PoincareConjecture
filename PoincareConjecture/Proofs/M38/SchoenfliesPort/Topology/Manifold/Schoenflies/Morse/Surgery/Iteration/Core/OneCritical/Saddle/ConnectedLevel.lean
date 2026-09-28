import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.OneCritical.Saddle.Level
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.OneCritical.SaddleEnds.ConnectedMiddle

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private theorem isPreconnected_fiber_of_small_bands
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {h : X → Real} (hh : Continuous h) {c ε : Real} (hε : 0 < ε)
    (hbands : ∀ η : Real, 0 < η → η ≤ ε →
      IsPreconnected (h ⁻¹' Icc (c - η) (c + η))) :
    IsPreconnected (h ⁻¹' {c}) := by
  rw [isPreconnected_iff_subset_of_fully_disjoint_closed (isClosed_singleton.preimage hh)]
  intro U V hU hV hcover hdis
  obtain ⟨Uo, Vo, hUo, hVo, hUUo, hVVo, hdiso⟩ := normal_separation hU hV hdis
  let K := h '' (Uo ∪ Vo)ᶜ
  have hK : IsCompact K := (hUo.union hVo).isClosed_compl.isCompact.image hh
  have hcK : c ∈ Kᶜ := by
    rintro ⟨x, hx, hxc⟩
    exact hx ((hcover hxc).imp (fun h => hUUo h) (fun h => hVVo h))
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hK.isClosed.isOpen_compl.mem_nhds hcK)
  let η := min ε (δ / 2)
  have hη : 0 < η := lt_min hε (half_pos hδ)
  have hηε : η ≤ ε := min_le_left _ _
  have hηδ : η < δ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hbandcover : h ⁻¹' Icc (c - η) (c + η) ⊆ Uo ∪ Vo := by
    intro x hx
    by_contra hxnot
    apply hball (show h x ∈ ball c δ from ?_) (mem_image_of_mem h hxnot)
    rw [mem_ball, Real.dist_eq]
    exact (abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩).trans_lt hηδ
  have hlevels : h ⁻¹' {c} ⊆ h ⁻¹' Icc (c - η) (c + η) := by
    intro x hx
    change h x = c at hx
    rw [mem_preimage, hx]
    exact ⟨by linarith, by linarith⟩
  rcases isPreconnected_iff_subset_of_disjoint.mp (hbands η hη hηε) Uo Vo hUo hVo
      hbandcover (by rw [hdiso.inter_eq, inter_empty]) with hleft | hright
  · left
    intro x hx
    rcases hcover hx with hxU | hxV
    · exact hxU
    · exact False.elim (Set.disjoint_left.mp hdiso (hleft (hlevels hx)) (hVVo hxV))
  · right
    intro x hx
    rcases hcover hx with hxU | hxV
    · exact False.elim (Set.disjoint_left.mp hdiso (hUUo hxU) (hright (hlevels hx)))
    · exact hxV

private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

namespace SphereMorseReduction

variable {f : S2 → E3} (M : SphereMorseReduction f)
    {g : S2 → E3} (hg : g ∈ M.tree.leaves)
    (P : SphereSurgeryPath (M.v : E3) (fun p => M.D (f p)) g)
    (hP : P.Protects ((fun p => inner Real (M.v : E3) (M.D (f p))) ''
      {p | mfderiv (𝓡 2) 𝓘(Real, Real)
        (fun q => inner Real (M.v : E3) (M.D (f q))) p = 0}))
    (hcaps : P.PreservesCaps) {p : S2} (hp : p ∈ P.core)
    (hc : mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun q => inner Real (M.v : E3) (g q)) p = 0)

include hg hP hcaps hp hc

theorem exists_connected_physical_critical_bands :
    ∃ ε : Real, 0 < ε ∧ ∀ η : Real, 0 < η → η ≤ ε →
      IsConnected ((fun q => inner Real (M.v : E3) (g q)) ⁻¹'
        Icc (inner Real (M.v : E3) (g p) - η) (inner Real (M.v : E3) (g p) + η)) := by
  obtain ⟨ε₁, hε₁, hfamilies⟩ := M.exists_terminal_annular_end_family hg P hP hcaps hp hc
  obtain ⟨ε₂, hε₂, hbandcore, _⟩ :=
    M.exists_physical_band_with_unique_critical_point hg P hP hcaps hp hc
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, ?_⟩
  intro η hη hηε
  obtain ⟨A, hlower, hupper⟩ := hfamilies η hη (hηε.trans (min_le_left _ _))
  have hη₂ : η ≤ ε₂ := hηε.trans (min_le_right _ _)
  have hsmallcore : (fun q => inner Real (M.v : E3) (g q)) ⁻¹'
      Icc (inner Real (M.v : E3) (g p) - η) (inner Real (M.v : E3) (g p) + η) ⊆ P.core := by
    intro q hq
    apply interior_subset (hbandcore ?_)
    exact ⟨by linarith [hq.1], by linarith [hq.2]⟩
  have hmiddle : A.middleRegion = (fun q => inner Real (M.v : E3) (g q)) ⁻¹'
      Icc (inner Real (M.v : E3) (g p) - η) (inner Real (M.v : E3) (g p) + η) := by
    ext q
    constructor
    · rintro ⟨hqC, hqh⟩
      change A.height q ∈ Icc A.lowerCut A.upperCut at hqh
      rwa [hlower, hupper, (A.height_germ q hqC).eq_of_nhds] at hqh
    · intro hq
      have hqC := hsmallcore hq
      refine ⟨hqC, ?_⟩
      change A.height q ∈ Icc A.lowerCut A.upperCut
      rwa [hlower, hupper, (A.height_germ q hqC).eq_of_nhds]
  refine ⟨⟨p, ?_⟩, ?_⟩
  · exact ⟨by linarith, by linarith⟩
  · rw [← hmiddle]
    exact A.isPreconnected_middleRegion (P.isConnected_core hcaps).isPreconnected P.isClosed_core

theorem isConnected_physical_critical_level :
    IsConnected {q | inner Real (M.v : E3) (g q) = inner Real (M.v : E3) (g p)} := by
  obtain ⟨ε, hε, hbands⟩ := M.exists_connected_physical_critical_bands hg P hP hcaps hp hc
  refine ⟨⟨p, rfl⟩, ?_⟩
  exact isPreconnected_fiber_of_small_bands
    ((innerSL Real (M.v : E3)).continuous.comp
      (M.tree.embedding_of_mem_leaves hg).contMDiff.continuous)
    hε (fun η hη hηε => (hbands η hη hηε).isPreconnected)

theorem connectedComponentIn_physical_critical_level :
    connectedComponentIn
        {q | inner Real (M.v : E3) (g q) = inner Real (M.v : E3) (g p)} p =
      {q | inner Real (M.v : E3) (g q) = inner Real (M.v : E3) (g p)} :=
  (M.isConnected_physical_critical_level hg P hP hcaps hp hc).isPreconnected.connectedComponentIn
    rfl

end SphereMorseReduction

end Poincare.Manifold.Schoenflies

end

end M38Schoenflies
