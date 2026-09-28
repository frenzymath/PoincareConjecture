import PoincareConjecture.Proofs.M47.SeedM15SafeCylinder









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function MeasureTheory
open scoped Manifold ContDiff Topology intervalIntegral

universe u

namespace PoincareConjecture.M47

open Proofs.M46 Proofs.M12



theorem SeedM15SafeCylinder.initial_scalar_bound
    {F : SurgeryFlowData.{u}} {T : ℝ} {hT : 0 < T} {hTF : T ∈ F.time_domain}
    {x : (F.slice T).carrier} {r : ℝ} {H : SeedM15TestHistory T hT hTF x r}
    {rho a budget : ℝ} {ha : 0 < a}
    (Q : SeedM15SafeCylinder H rho a ha) (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    (hrho : 0 < rho) (hthreshold : budget < rho ^ 2 / (16 * Real.sqrt a))
    {tau : ℝ} {y : H.spacetime.geometry.toLGeometry.Point}
    (p : M14BackwardPath H.spacetime.geometry.toLGeometry T 0 tau
      ((H.spacetime.geometry.sliceIdentification T).identification H.center).val y)
    (hbudget : (∫ t in 0..tau, Real.sqrt t * pathPositiveDensity p t) ≤ budget) :
    ∀ s ∈ Icc 0 tau, s ≤ a →
      horizontalScalarCurvature H.spacetime.geometry.toLGeometry.leafwise (p.curve s) ≤
        9 * rho⁻¹ ^ 2 := by
  let : CompactSpace (F.slice T).carrier :=
    isCompact_univ_iff.mp (F.slices_compact T hTF)
  let G := H.spacetime.geometry
  let b := Real.sqrt (min tau a)
  have hmin : 0 < min tau a := lt_min p.tau_lt ha
  have hb : 0 < b := Real.sqrt_pos.mpr hmin
  have hbtau : b ≤ Real.sqrt tau := Real.sqrt_le_sqrt (min_le_left _ _)
  have hba : b ≤ Real.sqrt a := Real.sqrt_le_sqrt (min_le_right _ _)
  have hclock : ∀ s ∈ Icc 0 b,
      G.realization.spacetime.timeFunction (p.curve (s ^ 2)) ∈
        (cylinderPhysicalInterval T 1 Q.cylinder.scale_pos
          (safeTestInterval a ha)).domain := by
    intro s hs
    have hsquare : s ^ 2 ≤ min tau a := by
      have hsq : b ^ 2 = min tau a := Real.sq_sqrt hmin.le
      nlinarith [hs.1, hs.2]
    rw [Q.physical_eq]
    change G.toLGeometry.spacetime.timeFunction (p.curve (s ^ 2)) ∈ Icc (T - a) T
    rw [p.curve_time (s ^ 2) ⟨sq_nonneg s, hsquare.trans (min_le_left _ _)⟩]
    constructor <;> nlinarith [hsquare.trans (min_le_right tau a), sq_nonneg s]
  have hzero : (0 : ℝ) ∈ (safeTestInterval a ha).domain := ⟨by linarith, le_rfl⟩
  let z : (G.realization.timeIntervals.interval
      (cylinderPhysicalInterval T 1 Q.cylinder.scale_pos (safeTestInterval a ha))).Point ×
        Q.source :=
    ((cylinderClockHomeomorph T 1 Q.cylinder.scale_pos (safeTestInterval a ha)).symm
      ⟨0, hzero⟩, ⟨x, Q.center_mem⟩)
  have hbase : p.curve 0 = rawCylinderMap G.realization Q.cylinder z := by
    rw [rawCylinderMap_at_parameter, Q.based, p.curve_start]
  have hpositive : (∫ t in 0..tau, Real.sqrt t * pathPositiveDensity p t) <
      rho ^ 2 / (16 * b) := by
    apply (hbudget.trans_lt hthreshold).trans_le
    exact div_le_div_of_nonneg_left (sq_nonneg rho) (mul_pos (by norm_num) hb)
      (mul_le_mul_of_nonneg_left hba (by norm_num))
  have hcapture := actualSafeCylinder_confines_initial_prefix G hM12 Q.cylinder Q.time_subset
    (F.metric T) hrho (by simpa only [one_mul] using Q.metric_lower)
    x Q.source_eq p hb hbtau hclock z hbase rfl hpositive
  intro s hs hsa
  have hsroot : Real.sqrt s ∈ Icc 0 b :=
    ⟨Real.sqrt_nonneg s, Real.sqrt_le_sqrt (le_min hs.2 hsa)⟩
  have hcap := hcapture hsroot
  change p.curve (Real.sqrt s ^ 2) ∈ range (rawCylinderMap G.realization Q.cylinder) at hcap
  rw [Real.sq_sqrt hs.1] at hcap
  obtain ⟨w, hw⟩ := hcap
  rw [← hw]
  exact Q.scalar_upper w

end PoincareConjecture.M47
