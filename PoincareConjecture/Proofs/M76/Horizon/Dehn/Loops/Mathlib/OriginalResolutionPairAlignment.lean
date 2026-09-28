import PoincareConjecture.Proofs.M76.Horizon.Dehn.Loops.Mathlib.OriginalResolutionWordExclusion
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Loops.Mathlib.ResolutionPairSelection
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Loops.Mathlib.ResolutionEndUniqueness
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Arcs.Mathlib.DisjointIntervalUniqueness

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn.PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "Q2" => sphere (0 : V2) 1
local notation "D2" => closedBall (0 : V2) 1
local notation "I01" => Icc (0 : ℝ) 1

theorem original_resolution_pair_excluded
    {X : Type*} [TopologicalSpace X] {Z : Set X} {base : Z}
    {G : Subgroup (FundamentalGroup Z base)} [G.Normal]
    {f : V2 → X} {c : Bool → P2 → V2} {τ : C3 → X}
    (D : OriginalResolutionWordExclusionData f Z base G c τ (1 / 4))
    (hf : ContinuousOn f D2) (hfZ : MapsTo f Q2 Z)
    {J K : Set V2}
    (qA : I01 ≃ₜ (D.A ∩ Q2 : Set V2)) (qC : I01 ≃ₜ (D.C ∩ Q2 : Set V2))
    (qD : I01 ≃ₜ J) (qB : I01 ≃ₜ K)
    (hqA0 : (qA 0 : V2) = c false (0, farArmParameter (!D.s0)))
    (hqA1 : (qA 1 : V2) = c false (1, farArmParameter (!D.s0)))
    (hqC0 : (qC 0 : V2) = c true (0, farArmParameter (!D.s1)))
    (hqC1 : (qC 1 : V2) = c true (1, farArmParameter (!D.s1)))
    (hqD0 : (qD 0 : V2) = c true (0, farArmParameter D.s1))
    (hqB1 : (qB 1 : V2) = c true (1, farArmParameter D.s1))
    (hJK : J ∪ K = D.M ∩ Q2)
    (aNew : Path D.E0.a D.E1.a) (cNew : Path D.E1.c D.E0.c)
    (haNew : ∀ t, (aNew t : X) = f (qA t))
    (hcNew : ∀ t, (cNew.symm t : X) = f (qC t))
    (RU RV : Path D.E0.c D.E0.c)
    (hU : RU.Homotopic (((D.E0.U.symm.trans aNew).trans D.E1.U).trans cNew))
    (hcases :
      (∃ (dNew : Path D.E0.l D.E0.r) (bNew : Path D.E1.r D.E1.l),
        (qD 1 : V2) = c false (0, farArmParameter D.s0) ∧
        (qB 0 : V2) = c false (1, farArmParameter D.s0) ∧
        (∀ t, (dNew t : X) = f (qD t)) ∧ (∀ t, (bNew t : X) = f (qB t)) ∧
        RV.Homotopic (((((((D.E0.R.symm.trans dNew.symm).trans D.E0.L).trans aNew).trans
          D.E1.L.symm).trans bNew.symm).trans D.E1.R).trans cNew)) ∨
      (∃ (dNew : Path D.E0.l D.E1.r) (bNew : Path D.E0.r D.E1.l),
        (qD 1 : V2) = c false (1, farArmParameter D.s0) ∧
        (qB 0 : V2) = c false (0, farArmParameter D.s0) ∧
        (∀ t, (dNew t : X) = f (qD t)) ∧ (∀ t, (bNew t : X) = f (qB t)) ∧
        RV.Homotopic (((((((D.E0.R.symm.trans bNew).trans D.E1.L).trans aNew.symm).trans
          D.E0.L.symm).trans dNew).trans D.E1.R).trans cNew)))
    (p : Path base D.E0.z) (q : Path base D.E1.z) :
    (p.trans D.E0.rc).whiskeredLoopClass RU ∉ G ∨
      (p.trans D.E0.rc).whiskeredLoopClass RV ∉ G := by
  have hQD : Q2 ⊆ D2 := sphere_subset_closedBall
  have hLQ : D.L ⊆ Q2 := (subset_union_left.trans D.middleRim.subset).trans inter_subset_right
  have hRQ : D.R ⊆ Q2 := (subset_union_right.trans D.middleRim.subset).trans inter_subset_right
  have hl0 : c false (0, farArmParameter D.s0) ∈ D.L := D.intervalL.1 (by simp)
  have hr1 : c false (1, farArmParameter D.s0) ∈ D.R := D.intervalR.1 (by simp)
  have huL : D.u ∈ D.L := D.intervalL.1 (by simp)
  have hvR : D.v ∈ D.R := D.intervalR.1 (by simp)
  have hC (cOld : Path D.E1.c D.E0.c)
      (hcOld : ∀ t, (cOld t : X) = f (D.pC.chart t)) : cNew.Homotopic cOld := by
    have h := marked_interval_chart_paths_homotopic qC
      (unitInterval.symmHomeomorph.trans D.pC.chart) hqC0 hqC1
      (by simpa using D.pC.chart_one) (by simpa using D.pC.chart_zero)
      f (hf.mono (inter_subset_right.trans hQD)) (fun _ hx ↦ hfZ hx.2)
      cNew.symm cOld.symm hcNew (fun t ↦ hcOld (unitInterval.symm t))
    simpa only [Path.symm_symm] using h.symm₂
  rcases D.cases with ⟨⟨hu, hv⟩, a, β, γ, d, ha, hβ, hγ, hd, _, _, hout⟩ |
    ⟨⟨hu, hv⟩, a, β, γ, d, ha, hβ, hγ, hd, _, _, hout⟩
  · obtain ⟨hJ, hK⟩ := disjoint_interval_charts_unique D.intervalL D.intervalR D.disjointLR
      (hJK.trans D.middleRim.symm) qD qB hqD0 hqB1 (hu ▸ huL) (hv ▸ hvR)
    subst J K
    have hA : aNew.Homotopic a := marked_interval_chart_paths_homotopic qA D.pA.chart
      hqA0 hqA1 D.pA.chart_zero D.pA.chart_one f
      (hf.mono (inter_subset_right.trans hQD)) (fun _ hx ↦ hfZ hx.2) aNew a haNew ha
    have hC' := hC γ hγ
    rcases hcases with ⟨dNew, bNew, hqD1, hqB0, hdNew, hbNew, hV⟩ |
      ⟨dNew, bNew, hqD1, hqB0, hdNew, hbNew, hV⟩
    · have hD : dNew.Homotopic d := marked_interval_chart_paths_homotopic qD
        (unitInterval.symmHomeomorph.trans D.pL.chart) hqD0 hqD1
        (by simpa using D.pL.chart_one.trans hu) (by simpa using D.pL.chart_zero)
        f (hf.mono (hLQ.trans hQD)) (fun _ hx ↦ hfZ (hLQ hx))
        dNew d hdNew hd
      have hB : bNew.Homotopic β := marked_interval_chart_paths_homotopic qB
        (unitInterval.symmHomeomorph.trans D.pR.chart) hqB0 hqB1
        (by simpa using D.pR.chart_one) (by simpa using D.pR.chart_zero.trans hv)
        f (hf.mono (hRQ.trans hQD)) (fun _ hx ↦ hfZ (hRQ hx))
        bNew β hbNew hβ
      apply actual_resolution_pair_excluded_case_a D.E0 D.E1 G p q a β γ d RU RV
      · exact hU.trans ((((Path.Homotopic.refl _).hcomp hA).hcomp (.refl _)).hcomp hC')
      · exact hV.trans ((((((((Path.Homotopic.refl _).hcomp hD.symm₂).hcomp (.refl _)).hcomp
          hA).hcomp (.refl _)).hcomp hB.symm₂).hcomp (.refl _)).hcomp hC')
      · exact hout p q
    · exact (Set.disjoint_left.mp D.disjointLR (hqD1 ▸ (qD 1).property) hr1).elim
  · obtain ⟨hJ, hK⟩ := disjoint_interval_charts_unique D.intervalR D.intervalL D.disjointLR.symm
      (hJK.trans (D.middleRim.symm.trans (union_comm D.L D.R))) qD qB hqD0 hqB1
      (hv ▸ hvR) (hu ▸ huL)
    subst J K
    have hA : aNew.Homotopic a.symm := marked_interval_chart_paths_homotopic qA D.pA.chart
      hqA0 hqA1 D.pA.chart_zero D.pA.chart_one f
      (hf.mono (inter_subset_right.trans hQD)) (fun _ hx ↦ hfZ hx.2) aNew a.symm haNew
      (fun t ↦ by simpa using ha (unitInterval.symm t))
    have hC' := hC γ hγ
    rcases hcases with ⟨dNew, bNew, hqD1, hqB0, hdNew, hbNew, hV⟩ |
      ⟨dNew, bNew, hqD1, hqB0, hdNew, hbNew, hV⟩
    · exact (Set.disjoint_left.mp D.disjointLR hl0 (hqD1 ▸ (qD 1).property)).elim
    · have hD : dNew.Homotopic d := marked_interval_chart_paths_homotopic qD D.pR.chart
        hqD0 hqD1 (D.pR.chart_zero.trans hv) D.pR.chart_one f
        (hf.mono (hRQ.trans hQD)) (fun _ hx ↦ hfZ (hRQ hx)) dNew d hdNew hd
      have hB : bNew.Homotopic β := marked_interval_chart_paths_homotopic qB D.pL.chart
        hqB0 hqB1 D.pL.chart_zero (D.pL.chart_one.trans hu) f
        (hf.mono (hLQ.trans hQD)) (fun _ hx ↦ hfZ (hLQ hx)) bNew β hbNew hβ
      apply actual_resolution_pair_excluded_case_b D.E0 D.E1 G p q a β γ d RU RV
      · exact hU.trans ((((Path.Homotopic.refl _).hcomp hA).hcomp (.refl _)).hcomp hC')
      · have hAi : aNew.symm.Homotopic a := by simpa only [Path.symm_symm] using hA.symm₂
        exact hV.trans ((((((((Path.Homotopic.refl _).hcomp hB).hcomp (.refl _)).hcomp
          hAi).hcomp (.refl _)).hcomp hD).hcomp (.refl _)).hcomp hC')
      · exact hout p q

end PoincareConjecture.M76.Dehn.PolygonalCrossingResolution
