import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_21_CompactCrossing
import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_21_CompactTimeCover
import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_21_OrdinaryNeighborhoods
import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.Prop16_4_RegularRegion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function MeasureTheory
open scoped Manifold ContDiff Topology intervalIntegral

universe u

namespace PoincareConjecture.Proofs.M46

open PoincareConjecture.Proofs.M12

def actionSublevelTrace {X : Type u} [TopologicalSpace X] {time : X → ℝ}
    {I : SpacetimeInterval} (G : GeneralizedLGeometryTransport 3 X time I)
    (T start : ℝ) (x : G.Point) (B : ℝ) : Set G.Point :=
  {v | ∃ tau, 0 < tau ∧ tau ≤ T - start ∧ ∃ y,
    ∃ p : M14BackwardPath G T 0 tau x y, M14BackwardLAction G p < B ∧
      ∃ s ∈ Icc 0 tau, p.curve s = v}

theorem actionConfinement_of_local_surgery_cages
    {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F}
    (H : M33RegularHistoryData W) (G : FlowBoxRicciGeometry H.generalized)
    {T start B energy : ℝ} {x : G.toLGeometry.Point}
    (hstart : 0 ≤ start) (hordered : start < T)
    (hwindow : Icc 0 T ⊆ H.generalized.interval)
    (hB : 3 * Real.sqrt (T - start) < B) (henergy : 0 ≤ energy)
    (hkinetic : ∀ tau, 0 < tau → tau ≤ T - start → ∀ y,
      ∀ p : M14BackwardPath G.toLGeometry T 0 tau x y,
        M14BackwardLAction G.toLGeometry p < B →
          IntervalIntegrable (M14.pathSquareKinetic p) volume 0 (Real.sqrt tau) ∧
            (∫ s in 0..Real.sqrt tau, M14.pathSquareKinetic p s) ≤ energy)
    (hsurgery : ∀ t ∈ Ico start T, t ∈ F.surgery_times →
      ∃ K : Set H.generalized.point, IsCompact K ∧
        (∀ v ∈ actionSublevelTrace G.toLGeometry T start x B, v.1 = t → v ∈ K) ∧
        ∃ N : Set H.generalized.point, IsCompact N ∧ ∃ delta : ℝ, 0 < delta ∧
          ∀ v ∈ actionSublevelTrace G.toLGeometry T start x B,
            v.1 ∈ Icc t (t + delta) → v ∈ N) :
    ∃ C : ActionConfinement G.toLGeometry T start x, C.barrier = B := by
  let Z := actionSublevelTrace G.toLGeometry T start x B
  have hclock : MapsTo (fun v : H.generalized.point => v.1) Z (Icc start T) := by
    rintro v ⟨tau, htau, hbound, y, p, haction, s, hs, rfl⟩
    have hp := p.curve_time s hs
    change (p.curve s).1 = T - s at hp
    change (p.curve s).1 ∈ Icc start T
    rw [hp]
    constructor <;> linarith [hs.1, hs.2]
  have hlocal : ∀ t ∈ Icc start T, ∃ N : Set H.generalized.point, IsCompact N ∧
      ∃ delta : ℝ, 0 < delta ∧ ∀ v ∈ Z, |v.1 - t| < delta → v ∈ N := by
    intro t ht
    by_cases hterminal : t = T
    · subst t
      obtain ⟨N, hN, _hinside, delta, hdelta, hcross⟩ :=
        exists_compact_crossing_neighborhood G.toLGeometry
          (isCompact_singleton : IsCompact ({x} : Set G.toLGeometry.Point))
          henergy (sub_nonneg.mpr hordered.le)
      refine ⟨N, hN, delta, hdelta, ?_⟩
      rintro v ⟨tau, htau, hbound, y, p, haction, s, hs, rfl⟩ hnear
      have hkin := hkinetic tau htau hbound y p haction
      apply hcross T tau x y p hbound hkin.1 hkin.2 0 ⟨le_rfl, htau.le⟩ s hs
      · have hp := p.curve_time s hs
        change (p.curve s).1 = T - s at hp
        simpa only [hp, show T - s - T = -s by ring, abs_neg, sub_zero] using hnear
      · simp only [p.curve_start, mem_singleton_iff]
    have htT : t < T := lt_of_le_of_ne ht.2 hterminal
    by_cases hevent : t ∈ F.surgery_times
    · obtain ⟨K, hK, hbirth, Npost, hpost, deltaPost, hdeltaPost, hpostCover⟩ :=
        hsurgery t ⟨ht.1, htT⟩ hevent
      obtain ⟨Npre, hpre, _hinside, deltaPre, hdeltaPre, hcross⟩ :=
        exists_compact_crossing_neighborhood G.toLGeometry hK henergy
          (sub_nonneg.mpr hordered.le)
      refine ⟨Npre ∪ Npost, hpre.union hpost, min deltaPre deltaPost,
        lt_min hdeltaPre hdeltaPost, ?_⟩
      intro v hv hnear
      by_cases hafter : t ≤ v.1
      · right
        apply hpostCover v hv
        exact ⟨hafter, by linarith [(abs_lt.mp hnear).2, min_le_right deltaPre deltaPost]⟩
      left
      have hbefore : v.1 < t := lt_of_not_ge hafter
      obtain ⟨tau, htau, hbound, y, p, haction, s, hs, rfl⟩ := hv
      have hp := p.curve_time s hs
      change (p.curve s).1 = T - s at hp
      have ha : T - t ∈ Icc 0 tau := by
        constructor
        · linarith
        · rw [hp] at hbefore
          linarith [hs.2]
      have hkin := hkinetic tau htau hbound y p haction
      apply hcross T tau x y p hbound hkin.1 hkin.2 (T - t) ha s hs
      · have heq : |s - (T - t)| = |T - s - t| := by
          rw [show s - (T - t) = -(T - s - t) by ring, abs_neg]
        rw [heq]
        exact (hp ▸ hnear).trans_le (min_le_left _ _)
      · apply hbirth (p.curve (T - t))
        · exact ⟨tau, htau, hbound, y, p, haction, T - t, ha, rfl⟩
        · have htime := p.curve_time (T - t) ha
          change (p.curve (T - t)).1 = T - (T - t) at htime
          simpa only [sub_sub_cancel] using htime
    · obtain ⟨N, hN, delta, hdelta, hcapture⟩ :=
        exists_compact_nonsurgery_clock_neighborhood H hwindow
          ⟨hstart.trans ht.1, htT⟩ hevent
      refine ⟨N, hN, delta, hdelta, ?_⟩
      intro v hv hnear
      exact hcapture v ⟨hstart.trans (hclock hv).1, (hclock hv).2⟩ hnear
  obtain ⟨K, hK, hcapture⟩ := exists_compact_of_local_time_cages hclock hlocal
  refine ⟨{
    barrier := B
    barrier_large := hB
    cage := K
    cage_compact := hK
    paths_mem := ?_
  }, rfl⟩
  intro tau htau hbound y p haction s hs
  exact hcapture ⟨tau, htau, hbound, y, p, haction, s, hs, rfl⟩

end PoincareConjecture.Proofs.M46
