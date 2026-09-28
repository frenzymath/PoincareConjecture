import PoincareConjecture.Proofs.M76.Mathlib.TorusCrossingBandCharts
import Mathlib.Topology.IsLocalHomeomorph

set_option autoImplicit false

open Set Geometry

namespace OpenPartialHomeomorph

theorem exists_union_localHomeomorph {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (e d : OpenPartialHomeomorph X Y) (heq : EqOn e d (e.source ∩ d.source)) :
    ∃ f : X → Y, IsLocalHomeomorphOn f (e.source ∪ d.source) ∧
      EqOn f e e.source ∧ EqOn f d d.source := by
  classical
  let f : X → Y := fun x => if x ∈ e.source then e x else d x
  have hfe : EqOn f e e.source := fun x hx => by simp only [f, if_pos hx]
  have hfd : EqOn f d d.source := by
    intro x hx
    by_cases hxe : x ∈ e.source
    · simpa only [f, if_pos hxe] using heq ⟨hxe, hx⟩
    · simp only [f, if_neg hxe]
  refine ⟨f, ?_, hfe, hfd⟩
  apply IsLocalHomeomorphOn.mk
  intro x hx
  rcases hx with hx | hx
  · exact ⟨e, hx, hfe⟩
  · exact ⟨d, hx, hfd⟩

end OpenPartialHomeomorph

namespace PLAnnularStrip

def crossingBandRegion (L d : ℝ) : Set (AddCircle (4 * L) × AddCircle (4 * L)) :=
  let arc := ((↑) : ℝ → AddCircle (4 * L)) '' Ioo (-d) d
  (univ ×ˢ arc) ∪ (arc ×ˢ univ)

theorem exists_crossingBand_immersion {L d : ℝ}
    (hL : 0 < L) (hd : 0 < d) (hwidth : 4 * d < L) (hcore : 6 * d ≤ L) :
    letI : Fact (0 < 4 * L) := ⟨by linarith⟩
    ∃ f : (AddCircle (4 * L) × AddCircle (4 * L)) → ℝ × ℝ,
      IsLocalHomeomorphOn f (crossingBandRegion L d) ∧
      (∀ s ∈ Ioo (-d) d, ∀ t ∈ Ioo (-d) d,
        f ((s : AddCircle (4 * L)), (t : AddCircle (4 * L))) = (s, t)) ∧
      ∀ a b : ℝ,
        let Q := (AddCircle.openPartialHomeomorphCoe (4 * L) a).prod
          (AddCircle.openPartialHomeomorphCoe (4 * L) b)
        LocallyPiecewiseAffineOn (f ∘ Q) (Q.source ∩ Q ⁻¹' crossingBandRegion L d) := by
  let : Fact (0 < 4 * L) := ⟨by linarith⟩
  obtain ⟨H, V, hHS, hVS, hagree, hHcore, _, hPL⟩ :=
    exists_crossing_torus_band_charts hL hd hwidth hcore
  obtain ⟨f, hf, hfH, hfV⟩ := H.exists_union_localHomeomorph V hagree
  have hU : H.source ∪ V.source = crossingBandRegion L d := by
    rw [hHS, hVS]
    rfl
  refine ⟨f, hU ▸ hf, ?_, ?_⟩
  · intro s hs t ht
    have hx : ((s : AddCircle (4 * L)), (t : AddCircle (4 * L))) ∈ H.source := by
      rw [hHS]
      exact ⟨mem_univ _, ⟨t, ht, rfl⟩⟩
    exact (hfH hx).trans (hHcore s hs t ht)
  · intro a b
    let Q := (AddCircle.openPartialHomeomorphCoe (4 * L) a).prod
      (AddCircle.openPartialHomeomorphCoe (4 * L) b)
    let U := Q.source ∩ Q ⁻¹' crossingBandRegion L d
    have hUopen : IsOpen U :=
      Q.continuousOn_toFun.isOpen_inter_preimage Q.open_source
        (hU ▸ H.open_source.union V.open_source)
    have hHQ := (mem_piecewiseAffineGroupoid_iff (ℝ × ℝ) (Q.trans H)).mp (hPL a b).1 |>.1
    have hVQ := (mem_piecewiseAffineGroupoid_iff (ℝ × ℝ) (Q.trans V)).mp (hPL a b).2 |>.1
    apply LocallyPiecewiseAffineOn.locality
    intro x hx
    have hside : Q x ∈ H.source ∪ V.source := by
      rw [hU]
      exact hx.2
    rcases hside with hside | hside
    · refine ⟨(Q.trans H).source, ⟨hx.1, hside⟩, ?_⟩
      apply (hHQ.mono (hUopen.inter (Q.trans H).open_source) inter_subset_right).congr
      intro y hy
      exact (hfH hy.2.2).symm
    · refine ⟨(Q.trans V).source, ⟨hx.1, hside⟩, ?_⟩
      apply (hVQ.mono (hUopen.inter (Q.trans V).open_source) inter_subset_right).congr
      intro y hy
      exact (hfV hy.2.2).symm

end PLAnnularStrip
