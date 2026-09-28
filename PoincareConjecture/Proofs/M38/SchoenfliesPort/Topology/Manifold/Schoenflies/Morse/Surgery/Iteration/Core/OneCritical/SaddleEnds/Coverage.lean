import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.OneCritical.SaddleEnds.Family
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.OneBoundary.Extrema







open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.PoincareConjecture

namespace M38Schoenflies



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1

variable {v : E3} {g : S2 → E3} {B : Set Real}



theorem exists_lower_end_through_point
    (L : List (SphereSurgeryCoreCap v g B))
    (hpair : L.Pairwise (fun D E => Disjoint
      (D.chart '' closedBall 0 1) (E.chart '' closedBall 0 1)))
    {C : Set S2} (hcore : C = (⋃ D ∈ L, D.chart '' ball 0 1)ᶜ)
    (hclosed : IsClosed C)
    {h : S2 → Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    (hgerm : ∀ p ∈ C, h =ᶠ[𝓝 p] (fun q => inner Real v (g q)))
    {a b : Real} (hab : a < b) (hlower : ∀ p ∈ C, a < h p)
    (hregular : ∀ p, h p ∈ Icc a b → mfderiv (𝓡 2) 𝓘(Real, Real) h p ≠ 0)
    (hcut : ∀ D ∈ L, D.center ≠ b)
    (ends : ∀ D ∈ L, D.center < b → LowerAnnularEnd D C h a b)
    {p : S2} (hpC : p ∈ C) (hpb : h p ≤ b) :
    ∃ (D : SphereSurgeryCoreCap v g B) (hD : D ∈ L) (hDb : D.center < b),
      p ∈ (ends D hD hDb).region := by
  obtain ⟨δ, hδ, F, hFs, _, _, hheight, hcomponent, hpF⟩ :=
    exists_smooth_regular_band_component_through_point hh hab hregular p
      ⟨(hlower p hpC).le, hpb⟩
  let K := F '' (univ ×ˢ Icc a b)
  have hsub : univ ×ˢ Icc a b ⊆ F.source := by
    rintro ⟨q, t⟩ ⟨_, ht⟩
    exact hFs ▸ ⟨mem_univ _, by linarith [ht.1], by linarith [ht.2]⟩
  have hK : IsCompact K := (isCompact_univ.prod isCompact_Icc).image_of_continuousOn
    (F.continuousOn.mono hsub)
  have hKtarget : K ⊆ F.target := by
    rintro y ⟨z, hz, rfl⟩
    exact F.map_source (hsub hz)
  have hKh (q : S2) (hq : q ∈ K) : h q ∈ Icc a b := by
    obtain ⟨⟨z, t⟩, ⟨_, ht⟩, rfl⟩ := hq
    rw [hheight z t ⟨by linarith [ht.1], by linarith [ht.2]⟩]
    exact ht
  obtain ⟨q, hq, hmin⟩ := (hK.inter_right hclosed).exists_isMinOn
    (show (K ∩ C).Nonempty from ⟨p, hpF, hpC⟩) hh.continuous.continuousOn
  have hqfront : q ∈ frontier C := by
    apply (mem_frontier_iff_notMem_interior hq.2).mpr
    intro hqint
    have hlocal : IsLocalMin h q := by
      filter_upwards [isOpen_interior.mem_nhds hqint,
        F.open_target.mem_nhds (hKtarget hq.1),
        (hh.continuous.isOpen_preimage _ isOpen_Ioi).mem_nhds (hlower q hq.2)] with y hyC hyF hyh
      by_cases hyb : h y ≤ b
      · apply hmin
        refine ⟨?_, interior_subset hyC⟩
        have hz := F.map_target hyF
        have hyt := hheight (F.symm y).1 (F.symm y).2 (hFs ▸ hz).2
        rw [F.right_inv hyF] at hyt
        refine ⟨F.symm y, ⟨mem_univ _, ?_⟩, F.right_inv hyF⟩
        rw [← hyt]
        exact ⟨le_of_lt hyh, hyb⟩
      · exact (hKh q hq.1).2.trans (le_of_lt (lt_of_not_ge hyb))
    exact hregular q (hKh q hq.1)
      (Poincare.Geometry.Manifold.mfderiv_eq_zero_of_isLocalMin hh hlocal)
  rw [frontier_core L hpair hcore] at hqfront
  simp only [mem_iUnion] at hqfront
  obtain ⟨D, hD, hqD⟩ := hqfront
  have hDheight : h q = D.center := ((hgerm q hq.2).eq_of_nhds).trans
    (D.height_eq_on_boundary q hqD)
  have hDb : D.center < b := lt_of_le_of_ne
    (hDheight ▸ (hKh q hq.1).2) (hcut D hD)
  let A := ends D hD hDb
  have hAK : A.band = K := by
    rw [LowerAnnularEnd.band, A.component q hqD]
    exact (connectedComponentIn_eq (hcomponent ▸ hq.1)).symm.trans hcomponent.symm
  have hpA : p ∈ A.band := hAK ▸ hpF
  obtain ⟨⟨z, t⟩, ⟨_, ht⟩, hzp⟩ := hpA
  have hpt : h p = t := hzp ▸ A.height z t
    ⟨by linarith [ht.1, A.delta_pos], by linarith [ht.2, A.delta_pos]⟩
  refine ⟨D, hD, hDb, ⟨(z, t), ⟨mem_univ _, ?_, ht.2⟩, hzp⟩⟩
  rw [← hpt, ← hDheight]
  exact hmin ⟨hpF, hpC⟩



theorem exists_lower_annular_end_family
    (L : List (SphereSurgeryCoreCap v g B))
    (hpair : L.Pairwise (fun D E => Disjoint
      (D.chart '' closedBall 0 1) (E.chart '' closedBall 0 1)))
    {C : Set S2} (hcore : C = (⋃ D ∈ L, D.chart '' ball 0 1)ᶜ)
    (hC : IsPreconnected C) (hclosed : IsClosed C)
    {h : S2 → Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    (hgerm : ∀ p ∈ C, h =ᶠ[𝓝 p] (fun q => inner Real v (g q)))
    {a b : Real} (hab : a < b)
    (hlower : ∀ p ∈ C, a < h p) (hgreater : ∃ p ∈ C, b < h p)
    (hregular : ∀ p, h p ∈ Icc a b → mfderiv (𝓡 2) 𝓘(Real, Real) h p ≠ 0)
    (hcut : ∀ D ∈ L, D.center ≠ b) :
    ∃ ends : ∀ D ∈ L, D.center < b → LowerAnnularEnd D C h a b,
      (∀ D hD hDb E hE hEb, D ≠ E →
        Disjoint (ends D hD hDb).region (ends E hE hEb).region) ∧
      (⋃ D, ⋃ hD : D ∈ L, ⋃ hDb : D.center < b, (ends D hD hDb).region) =
        C ∩ h ⁻¹' Iic b := by
  classical
  let ends : ∀ D ∈ L, D.center < b → LowerAnnularEnd D C h a b :=
    fun D hD hDb => Classical.choice (exists_lowerAnnularEnd L hpair hcore hC hclosed
      hh hgerm hab (fun p hp => (hlower p hp).le) hgreater hregular D hD hDb)
  have hcenter (D : SphereSurgeryCoreCap v g B) (hD : D ∈ L) : a ≤ D.center := by
    obtain ⟨q, hq⟩ := D.isConnected_boundary.nonempty
    have hqC := ((core_inter_closed_disk L hpair hcore D hD).superset hq).1
    have hqh := ((hgerm q hqC).eq_of_nhds).trans (D.height_eq_on_boundary q hq)
    exact hqh ▸ (hlower q hqC).le
  refine ⟨ends, ?_, ?_⟩
  · intro D hD hDb E hE hEb hne
    exact (ends D hD hDb).disjoint_region L hpair hcore hh.continuous hgerm
      (ends E hE hEb) hD hE (hcenter D hD) (hcenter E hE) hDb hEb hne
  · ext p
    constructor
    · simp only [mem_iUnion]
      rintro ⟨D, hD, hDb, hp⟩
      refine ⟨(ends D hD hDb).retained hp, ?_⟩
      obtain ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩ := hp
      change h ((ends D hD hDb).chart (q, t)) ≤ b
      rw [(ends D hD hDb).height q t
        ⟨by linarith [(ends D hD hDb).delta_pos, hcenter D hD, ht.1],
          by linarith [(ends D hD hDb).delta_pos, ht.2]⟩]
      exact ht.2
    · rintro ⟨hpC, hpb⟩
      obtain ⟨D, hD, hDb, hp⟩ := exists_lower_end_through_point L hpair hcore hclosed
        hh hgerm hab hlower hregular hcut ends hpC hpb
      exact mem_iUnion_of_mem D (mem_iUnion_of_mem hD (mem_iUnion_of_mem hDb hp))

end Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap

end

end M38Schoenflies
