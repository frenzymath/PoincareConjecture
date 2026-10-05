import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.PuncturedTorusCompression
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.CenteredTorusPLPullback

/-!
# A PL immersion of the punctured two-torus with a fixed core

The actual supported square compression takes the punctured
torus into the two crossing bands. Compose it with their
constructed immersion. Standard quotient coordinates have
locally PL formulas on the compression chart and on its fixed
exterior, and these cover the entire punctured domain. See
Hatcher p. 7, Hamilton 1976, p. 66 and M76 derivation 270.
-/

set_option autoImplicit false

open Set Geometry

namespace PLAnnularStrip

/-- The actual two-torus with its opposite-center point
removed has a PL local homeomorphism to the plane which
retains a whole central coordinate square. PL regularity is
proved on the full standard quotient-coordinate domains.
See Hatcher p. 7, Hamilton p. 66 and M76 derivation 270. -/
theorem exists_punctured_torus_PL_immersion {L d : ℝ}
    (hL : 0 < L) (hd : 0 < d) (hwidth : 4 * d < L) (hcore : 6 * d ≤ L) :
    letI : Fact (0 < 4 * L) := ⟨by linarith⟩
    let q := AddCircle.centeredSquareQuotient (4 * L) 0
    ∃ f : (AddCircle (4 * L) × AddCircle (4 * L)) → ℝ × ℝ,
      IsLocalHomeomorphOn f {q}ᶜ ∧
      (∀ s ∈ Ioo (-d / 2) (d / 2), ∀ t ∈ Ioo (-d / 2) (d / 2),
        f ((s : AddCircle (4 * L)), (t : AddCircle (4 * L))) = (s, t)) ∧
      ∀ a b : ℝ,
        let T := (AddCircle.openPartialHomeomorphCoe (4 * L) a).prod
          (AddCircle.openPartialHomeomorphCoe (4 * L) b)
        LocallyPiecewiseAffineOn (f ∘ T) (T.source ∩ T ⁻¹' {q}ᶜ) := by
  let : Fact (0 < 4 * L) := ⟨by linarith⟩
  let Q := AddCircle.centeredSquareQuotient (4 * L)
  let K := {x : ℝ × ℝ | ‖x‖ ≤ (4 * L) / 2 - d / 2}
  let O := (Q '' K)ᶜ
  have hdhalf : d < (4 * L) / 2 := by linarith
  have hRB : (4 * L) / 2 - d / 2 < (4 * L) / 2 := by linarith
  have hKS : K ⊆ Q.source :=
    AddCircle.closedSquare_subset_centeredSquareQuotient_source (4 * L) hRB
  have hO : IsOpen O :=
    (AddCircle.isCompact_centeredSquareQuotient_closedSquare (4 * L) hRB).isClosed.isOpen_compl
  have hOU : O ⊆ crossingBandRegion L d :=
    compl_centeredSquareImage_subset_crossingBand hL hd hdhalf (by linarith)
  obtain ⟨H, C, hHS, hHT, hHPL, hC, hCimage, hCchart, hCfix, hCcore⟩ :=
    exists_punctured_torus_compression hL hd hdhalf
  let e := Q.symm.trans (H.trans Q)
  obtain ⟨F, hF, hFcore, hFPL⟩ := exists_crossingBand_immersion hL hd hwidth hcore
  have hFQ : LocallyPiecewiseAffineOn (F ∘ Q)
      (Q.source ∩ Q ⁻¹' crossingBandRegion L d) :=
    AddCircle.locallyPiecewiseAffineOn_comp_centeredSquareQuotient (4 * L)
      F (crossingBandRegion L d) (hFPL 0 0)
  have hHQ : Q '' H.target ⊆ crossingBandRegion L d := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hHT] at hx
    exact (centeredSquareQuotient_mem_crossingBand_iff hL hd hdhalf hx.2).mpr hx.1
  have hES (z : AddCircle (4 * L) × AddCircle (4 * L))
      (hzQ : z ∈ Q.target)
      (hz : z ∈ ({Q 0} : Set (AddCircle (4 * L) × AddCircle (4 * L)))ᶜ) :
      z ∈ e.source := by
    have hxQ : Q.symm z ∈ Q.source := Q.map_target hzQ
    have hxB : ‖Q.symm z‖ < (4 * L) / 2 := by
      simpa only [Q, AddCircle.centeredSquareQuotient_source, mem_ofPred_eq] using hxQ
    have hxne : Q.symm z ≠ 0 := by
      intro he
      apply hz
      exact mem_singleton_iff.mpr ((Q.right_inv hzQ).symm.trans (congrArg Q he))
    have hxH : Q.symm z ∈ H.source := by
      rw [hHS]
      exact ⟨norm_pos_iff.mpr hxne, hxB⟩
    refine ⟨hzQ, hxH, ?_⟩
    rw [AddCircle.centeredSquareQuotient_source]
    have hxT := H.map_source hxH
    rw [hHT] at hxT
    exact hxT.2
  refine ⟨F ∘ C, hF.comp hC hCimage, ?_, ?_⟩
  · intro s hs t ht
    have hzcore : ((s : AddCircle (4 * L)), (t : AddCircle (4 * L))) ∈
        crossingBandRegion L (d / 2) := by
      exact Or.inl ⟨mem_univ _, ⟨t, ⟨by linarith [ht.1], ht.2⟩, rfl⟩⟩
    change F (C ((s : AddCircle (4 * L)), (t : AddCircle (4 * L)))) = (s, t)
    rw [hCcore hzcore]
    exact hFcore s ⟨by linarith [hs.1], by linarith [hs.2]⟩
      t ⟨by linarith [ht.1], by linarith [ht.2]⟩
  · intro a b
    let T := (AddCircle.openPartialHomeomorphCoe (4 * L) a).prod
      (AddCircle.openPartialHomeomorphCoe (4 * L) b)
    let D := T.trans Q.symm
    let U := T.source ∩ T ⁻¹' {Q 0}ᶜ
    have hU : IsOpen U :=
      T.continuousOn_toFun.isOpen_inter_preimage T.open_source isClosed_singleton.isOpen_compl
    have hDPL : LocallyPiecewiseAffineOn D D.source :=
      (mem_piecewiseAffineGroupoid_iff (ℝ × ℝ) D).mp
        (AddCircle.centeredSquareQuotient_transition_mem_piecewiseAffineGroupoid (4 * L) a b) |>.1
    have hH : LocallyPiecewiseAffineOn H H.source :=
      (mem_piecewiseAffineGroupoid_iff (ℝ × ℝ) H).mp hHPL |>.1
    have hinside := (hFQ.comp hH).comp hDPL
    apply LocallyPiecewiseAffineOn.locality
    intro x hx
    by_cases hzQ : T x ∈ Q.target
    · let V := (T.trans e).source
      have hxV : x ∈ V := ⟨hx.1, hES (T x) hzQ hx.2⟩
      refine ⟨V, hxV, ?_⟩
      have hsub : U ∩ V ⊆ D.source ∩ D ⁻¹'
          (H.source ∩ H ⁻¹' (Q.source ∩ Q ⁻¹' crossingBandRegion L d)) := by
        intro y hy
        have hzE : T y ∈ e.source := hy.2.2
        change (T y ∈ Q.target ∧ Q.symm (T y) ∈ H.source ∧
          H (Q.symm (T y)) ∈ Q.source) at hzE
        refine ⟨⟨hy.2.1, hzE.1⟩, hzE.2.1, hzE.2.2, ?_⟩
        exact hHQ ⟨H (Q.symm (T y)), H.map_source hzE.2.1, rfl⟩
      apply (hinside.mono (hU.inter (T.trans e).open_source) hsub).congr
      intro y hy
      change F (Q (H (Q.symm (T y)))) = F (C (T y))
      exact congrArg F (hCchart hy.2.2).symm
    · have hzO : T x ∈ O := by
        rintro ⟨y, hyK, he⟩
        exact hzQ (he ▸ Q.map_source (hKS hyK))
      let V := T.source ∩ T ⁻¹' O
      have hV : IsOpen V := T.continuousOn_toFun.isOpen_inter_preimage T.open_source hO
      refine ⟨V, ⟨hx.1, hzO⟩, ?_⟩
      have hsub : U ∩ V ⊆ T.source ∩ T ⁻¹' crossingBandRegion L d :=
        fun _ hy => ⟨hy.2.1, hOU hy.2.2⟩
      apply ((hFPL a b).mono (hU.inter hV) hsub).congr
      intro y hy
      change F (T y) = F (C (T y))
      exact congrArg F (hCfix hy.2.2).symm

end PLAnnularStrip
