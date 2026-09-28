import PoincareConjecture.Proofs.M65.Sec19_5_GoodTimes.FamilyCellLimit
import PoincareConjecture.Proofs.M65.Sec19_5_GoodTimes.LimitLoopFamily
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.AreaContinuity.FillingLimit
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.AreaContinuity.Relabeling
import PoincareConjecture.Proofs.M65.Claim19_23_SweptArea.FillingWitnesses











set_option autoImplicit false

open Set Filter Bundle
open scoped Topology ContDiff Manifold

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ} {F : RicciFlow 3 M (Icc a b)}
  {Gamma : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))} {zeta : ℝ}

set_option maxHeartbeats 1600000 in






theorem m65FamilyCell_exists_filled_limit (hM64 : M64ComparisonTheory.{u})
    (compact : IsCompact (univ : Set M)) (V : M64ThreeDimensionalFlowConclusion F)
    (C : M63FamilyConclusion V.flow.geometry Gamma zeta)
    (circumference : ℕ → ℝ) (h : ∀ k, 0 < circumference k)
    (hlt : ∀ k, circumference k < 1) (hzero : Tendsto circumference atTop (𝓝 0))
    (z : LoopTwoSphere) {r s ell : ℝ} (hrs : r ≤ s)
    (hsub : Icc r s ⊆ Ioo a b) (hell : 0 < ell)
    (hlength : ∀ k, ell ≤ m62Length
      (V.flow.geometry.product (circumference k) (h k)).flow
      ((C.solutions (circumference k) (h k)).curve z) r)
    (B : ℕ → ℝ) (hB : ∀ i, 0 ≤ B i)
    (hjets : ∀ k t x, t ∈ Icc r s → ∀ i,
      m63CurvatureJetSquared (V.flow.geometry.product (circumference k) (h k)).flow
        ((C.solutions (circumference k) (h k)).curve z) i t x ≤ B i) :
    ∃ select : ℕ → ℕ, StrictMono select ∧
      ∃ L : M65SmoothFilledLoopFamily F (Ioo r s),
        (∀ t ∈ Ioo r s, ∀ x,
          curveVelocity (n := 3) (fun q => periodicFreeLoop (L.loops q) x) t =
            m62CurvatureVector F (fun y q => periodicFreeLoop (L.loops q) y) t x) ∧
        ∀ t : Ioo r s, Tendsto
          (fun k => fillingArea (F.metric t)
            ((C.solutions (circumference (select k)) (h (select k))).projected
              ⟨t, Ioo_subset_Icc_self (hsub (Ioo_subset_Icc_self t.property))⟩ z))
          atTop (𝓝 (fillingArea (F.metric t) (L.loops t))) := by
  classical
  let G := V.flow.geometry
  let P (k : ℕ) := G.product (circumference k) (h k)
  obtain ⟨phi, hphi, hc, hinit, vmin, vmax, hvmin, hvmax, hspeed, hj, hslope⟩ :=
    m65FamilyCell_normalization_bounds C circumference h hlt hzero z hrs hsub hell
      hlength B hB hjets
  let c := fun k x t => (C.solutions (circumference k) (h k)).curve z (phi k x) t
  have hC : 0 ≤ (3 : ℝ) ^ 2 * G.K0 := mul_nonneg (sq_nonneg _) G.nonnegative.1
  have hRm (t : ℝ) (ht : t ∈ Icc r s) (p : M) :
      (F.connection t).curvatureTensorNorm p ≤ (3 : ℝ) ^ 2 * G.K0 :=
    m65CurvatureTensorNorm_le_of_ambient_bounds G.bounds G.nonnegative.1
      (Ioo_subset_Icc_self (hsub ht)) p
  obtain ⟨select, hselect, clim, hpoint, hsmooth, hperiod, hgeom, hchart⟩ :=
    m65Projected_exists_smooth_curveShortening_limit compact P c hc hrs hsub hC hRm
      (fun k => m62Length (P k).flow
        ((C.solutions (circumference k) (h k)).curve z) r / curvePeriod)
      hinit ⟨vmax, hvmax, fun k t x ht => (hspeed k t x ht).2⟩ hj hvmin
      (fun k t x ht => (hspeed k t x ht).1)
      (fun t ht x => hslope t (Ioo_subset_Icc_self ht) x)
  let Ω : Set (ℝ × ℝ) := Ioo r s ×ˢ univ
  have hproj (k : ℕ) : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 3) ∞
      (fun w => (c k w.2 w.1).1) Ω := by
    let := (P k).charts.chartedSpace
    have hfst : ContMDiff (𝓡 4) (𝓡 3) ∞ (Prod.fst : (P k).charts.Point → M) :=
      contMDiff_fst.comp (P k).charts.to_product_smooth
    have hswap : ContDiff ℝ ∞ (fun w : ℝ × ℝ => (w.2, w.1)) :=
      contDiff_snd.prodMk contDiff_fst
    exact hfst.comp_contMDiffOn ((hc k).joint_smooth.comp hswap.contMDiff.contMDiffOn
      (fun w hw => ⟨mem_univ _, hsub (Ioo_subset_Icc_self hw.1)⟩))
  let q : C(Ω, M) := ⟨fun w => clim w.1.2 w.1.1, hsmooth.continuousOn.domRestrict⟩
  obtain ⟨B1, hB1, hcurv⟩ := hj 1
  have hC0 := m65Projected_tendsto_continuousMap compact
    (fun k => P (select k)) (fun k => c (select k)) (fun k => hc (select k))
    hrs hsub hC hvmax hB1 hRm
    (fun k t x ht => (le_abs_self _).trans (hspeed (select k) t x ht).2)
    (fun k t x ht => hcurv (select k) t x ht) q
    (fun w => hpoint w.1.1 w.property.1 w.1.2)
  have hbase (t : ℝ) (ht : t ∈ Ioo r s) (x : ℝ) :
      Tendsto (fun p : ℕ × ℝ => (c (select p.1) p.2 t).1)
        (atTop ×ˢ 𝓝 x) (𝓝 (clim x t)) :=
    m65ContinuousMap_joint_time _ q hC0 ht x
  let time (t : Ioo r s) : Icc a b :=
    ⟨t, Ioo_subset_Icc_self (hsub (Ioo_subset_Icc_self t.property))⟩
  have hrab : r ∈ Icc a b := Ioo_subset_Icc_self (hsub ⟨le_rfl, hrs⟩)
  obtain ⟨loops, hloops⟩ := m65PeriodicFamily_exists_loops isOpen_Ioo clim hsmooth hperiod
    ((C.solutions (circumference 0) (h 0)).projected ⟨r, hrab⟩ z)
  have hp (k : ℕ) (t : Ioo r s) : Function.Periodic (fun x => (c k x t).1) curvePeriod :=
    fun x => congrArg Prod.fst ((hc k).periodic t (time t).property x)
  let loopsN (k : ℕ) (t : Ioo r s) : C1FreeLoopSpace (M := M) :=
    m65LoopOfPeriodic (fun x => (c k x t).1)
      (m65TimeSlice_contMDiff isOpen_Ioo (fun x t => (c k x t).1) (hproj k) t.property) (hp k t)
  have heval (k : ℕ) (t : Ioo r s) (x : ℝ) :
      periodicFreeLoop (loopsN k t) x = (c k x t).1 :=
    m65PeriodicFreeLoop_loopOfPeriodic _ _ _ x
  have hconv (t : Ioo r s) : Tendsto (fun k => loopsN (select k) t) atTop (𝓝 (loops t)) := by
    apply m65C1Loop_tendsto_of_local_chart_jets isOpen_Ioo
      (fun k w => (c (select k) w.2 w.1).1) (fun w => clim w.2 w.1)
      (fun k => hproj (select k)) hsmooth hbase ?_ t.property _ _
      (fun k => heval (select k) t) (hloops t t.property)
    intro w hw
    obtain ⟨p, J, U, hJ, hU, hwJ, hwU, hJU, hsource, hjet⟩ := hchart w hw
    exact ⟨p, J, U, hJ, hU, hwJ, hwU, hJU, hsource, hjet 1⟩
  have hrelabel (k : ℕ) (t : Ioo r s) (v : LoopCircle) :
      loopsN k t v = (C.solutions (circumference k) (h k)).projected (time t) z
        (m65CircleRelabeling (phi k) (hphi k).2.1 v) := by
    apply m65CircleRelabeling_loop_values (phi k) (hphi k).2.1 _ _ ?_ v
    intro x
    rw [heval]
    exact ((C.solutions (circumference k) (h k)).projected_eq (time t) z (phi k x)).symm
  have hfilledN (k : ℕ) (t : Ioo r s) :
      Nonempty (LipschitzSpanningDisk (F.metric t) (loopsN k t)) :=
    (m65RelabelSpanningDisk_nonempty_iff (m65CircleRelabeling (phi k) (hphi k).2.1)
      (hrelabel k t)).mpr
        (m65ProjectedDisk_nonempty hM64 compact (C.solutions (circumference k) (h k)) (time t) z)
  have harea (k : ℕ) (t : Ioo r s) : fillingArea (F.metric t) (loopsN k t) =
      fillingArea (F.metric t) ((C.solutions (circumference k) (h k)).projected (time t) z) :=
    m65FillingArea_relabel (m65CircleRelabeling (phi k) (hphi k).2.1) (hrelabel k t)
  have hlimit (t : Ioo r s) :
      Nonempty (LipschitzSpanningDisk (F.metric t) (loops t)) ∧
        Tendsto (fun k => fillingArea (F.metric t)
          ((C.solutions (circumference (select k)) (h (select k))).projected (time t) z))
          atTop (𝓝 (fillingArea (F.metric t) (loops t))) := by
    have hd := m65FillingArea_tendsto_of_C1 (P 0) t
      (V.disks (circumference 0) (h 0) t (time t).property) compact
      (fun k => loopsN (select k) t) (loops t) (hconv t)
      (fun k => hfilledN (select k) t)
    exact ⟨hd.1, hd.2.congr' (Eventually.of_forall (fun k => harea (select k) t))⟩
  obtain ⟨L, hL, heq⟩ := m65SmoothFilledLoopFamily_of_values F isOpen_Ioo clim hsmooth
    (fun t ht x => (hgeom t ht x).2) loops hloops (fun t ht => (hlimit ⟨t, ht⟩).1)
  refine ⟨select, hselect, L, heq, ?_⟩
  intro t
  rw [hL]
  exact (hlimit t).2

end PoincareConjecture
