import PoincareConjecture.Proofs.M76.Mathlib.PuncturedTorusCompression
import PoincareConjecture.Proofs.M76.Mathlib.CenteredTorusPLPullback
import PoincareConjecture.Proofs.M76.Mathlib.AddCirclePLCharts

set_option autoImplicit false

open Set Geometry

namespace AddCircle

theorem exists_bounded_core_fixed_puncturedCircle_chart
    (p : ℝ) [Fact (0 < p)] (r : ℝ) (hr : r < p / 2) :
    ∃ (e : OpenPartialHomeomorph (AddCircle p) ℝ) (K : Set ℝ),
      e.source = {((-p / 2 : ℝ) : AddCircle p)}ᶜ ∧
      e.target = Ioo (-p / 2) (p / 2) ∧ IsCompact K ∧
      e '' e.source ⊆ K ∧
      (∀ x ∈ Icc (-r) r, (x : AddCircle p) ∈ e.source ∧ e x = x) ∧
      ∀ a : ℝ, (openPartialHomeomorphCoe p a).trans e ∈ piecewiseAffineGroupoid ℝ := by
  obtain ⟨e, hsource, htarget, hcore, hPL⟩ :=
    exists_core_fixed_puncturedCircle_chart p r hr
  refine ⟨e, Icc (-p / 2) (p / 2), hsource, htarget, isCompact_Icc, ?_, hcore, hPL⟩
  rintro _ ⟨x, hx, rfl⟩
  have hy := e.map_source hx
  rw [htarget] at hy
  exact ⟨hy.1.le, hy.2.le⟩

end AddCircle

namespace PLAnnularStrip

theorem exists_bounded_punctured_torus_PL_immersion {L d D : ℝ}
    (hL : 0 < L) (hd : 0 < d) (hdD : d < D)
    (hwidth : 4 * D < L) (hcore : 6 * D ≤ L) :
    letI : Fact (0 < 4 * L) := ⟨by linarith⟩
    let q := AddCircle.centeredSquareQuotient (4 * L) 0
    ∃ (f : (AddCircle (4 * L) × AddCircle (4 * L)) → ℝ × ℝ) (B : Set (ℝ × ℝ)),
      IsLocalHomeomorphOn f {q}ᶜ ∧ IsCompact B ∧ f '' {q}ᶜ ⊆ B ∧
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
  let arc := ((↑) : ℝ → AddCircle (4 * L)) '' Icc (-d) d
  let N : Set (AddCircle (4 * L) × AddCircle (4 * L)) :=
    (univ ×ˢ arc) ∪ (arc ×ˢ univ)
  have harc : IsCompact arc := isCompact_Icc.image (AddCircle.continuous_mk' (4 * L))
  have hN : IsCompact N :=
    (isCompact_univ.prod harc).union (harc.prod isCompact_univ)
  have hUN : crossingBandRegion L d ⊆ N := by
    rintro z (hz | hz)
    · rcases hz.2 with ⟨t, ht, he⟩
      exact Or.inl ⟨mem_univ _, t, ⟨ht.1.le, ht.2.le⟩, he⟩
    · rcases hz.1 with ⟨s, hs, he⟩
      exact Or.inr ⟨⟨s, ⟨hs.1.le, hs.2.le⟩, he⟩, mem_univ _⟩
  have hNW : N ⊆ crossingBandRegion L D := by
    rintro z (hz | hz)
    · rcases hz.2 with ⟨t, ht, he⟩
      exact Or.inl ⟨mem_univ _, t, ⟨by linarith [ht.1], by linarith [ht.2]⟩, he⟩
    · rcases hz.1 with ⟨s, hs, he⟩
      exact Or.inr ⟨⟨s, ⟨by linarith [hs.1], by linarith [hs.2]⟩, he⟩, mem_univ _⟩
  have hUW := hUN.trans hNW
  obtain ⟨H, C, hHS, hHT, hHPL, hC, hCimage, hCchart, hCfix, hCcore⟩ :=
    exists_punctured_torus_compression hL hd hdhalf
  let e := Q.symm.trans (H.trans Q)
  obtain ⟨F, hF, hFcore, hFPL⟩ :=
    exists_crossingBand_immersion hL (hd.trans hdD) hwidth hcore
  have hFQ : LocallyPiecewiseAffineOn (F ∘ Q)
      (Q.source ∩ Q ⁻¹' crossingBandRegion L D) :=
    AddCircle.locallyPiecewiseAffineOn_comp_centeredSquareQuotient (4 * L)
      F (crossingBandRegion L D) (hFPL 0 0)
  have hHQ : Q '' H.target ⊆ crossingBandRegion L D := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hHT] at hx
    exact hUW ((centeredSquareQuotient_mem_crossingBand_iff hL hd hdhalf hx.2).mpr hx.1)
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
  refine ⟨F ∘ C, F '' N, hF.comp hC (fun z hz => hUW (hCimage hz)),
    hN.image_of_continuousOn (hF.continuousOn.mono hNW), ?_, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact ⟨C z, hUN (hCimage hz), rfl⟩
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
    let A := T.trans Q.symm
    let U := T.source ∩ T ⁻¹' {Q 0}ᶜ
    have hU : IsOpen U :=
      T.continuousOn_toFun.isOpen_inter_preimage T.open_source isClosed_singleton.isOpen_compl
    have hAPL : LocallyPiecewiseAffineOn A A.source :=
      (mem_piecewiseAffineGroupoid_iff (ℝ × ℝ) A).mp
        (AddCircle.centeredSquareQuotient_transition_mem_piecewiseAffineGroupoid (4 * L) a b) |>.1
    have hH : LocallyPiecewiseAffineOn H H.source :=
      (mem_piecewiseAffineGroupoid_iff (ℝ × ℝ) H).mp hHPL |>.1
    have hinside := (hFQ.comp hH).comp hAPL
    apply LocallyPiecewiseAffineOn.locality
    intro x hx
    by_cases hzQ : T x ∈ Q.target
    · let V := (T.trans e).source
      have hxV : x ∈ V := ⟨hx.1, hES (T x) hzQ hx.2⟩
      refine ⟨V, hxV, ?_⟩
      have hsub : U ∩ V ⊆ A.source ∩ A ⁻¹'
          (H.source ∩ H ⁻¹' (Q.source ∩ Q ⁻¹' crossingBandRegion L D)) := by
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
      have hsub : U ∩ V ⊆ T.source ∩ T ⁻¹' crossingBandRegion L D :=
        fun _ hy => ⟨hy.2.1, hUW (hOU hy.2.2)⟩
      apply ((hFPL a b).mono (hU.inter hV) hsub).congr
      intro y hy
      change F (T y) = F (C (T y))
      exact congrArg F (hCfix hy.2.2).symm

end PLAnnularStrip
