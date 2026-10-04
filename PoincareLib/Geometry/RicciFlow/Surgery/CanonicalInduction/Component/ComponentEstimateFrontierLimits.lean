import PoincareLib.Topology.Manifold.Poincare.Final.Compatibility.SourceNames
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.StableSet.Cylinders.CylinderScalarCalculus
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.StableSet.Seed.CylinderMetric
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Cylinder.EventNeighborhood
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.CanonicalTheory

/-!
# Closed bounds at the first included cylinder time

The actual ordinary right slab fixes the point and tangent before taking
a limit. No retained preimage at the first time is needed.
Source: Definition 3.1, Lemma 3.15 and Definition 15.2, used on pp. 402-405.
See `proof-work/tasks/M47/derivations/component-frontier.md`, Stage F1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M47

open Proofs.M46

variable {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {origin a : ℝ} {U : Set C.carrier}

private theorem exists_component_right_slab
    (e : SurgeryFlowCylinder F C origin 1 (Icc a 0) U) (ha : a < 0) :
    ∃ r : ℝ, a < r ∧ r < 0 ∧
      Disjoint F.surgery_times (Ioc (origin + a / 1) (origin + r / 1)) := by
  have hab : origin + a / 1 < origin + 0 / 1 := by simp only [div_one]; linarith
  obtain ⟨b, hab, hb0, hfree⟩ := M44.exists_surgery_free_right_interval F
    (e.time_subset (mem_image_of_mem _ (show a ∈ Icc a 0 from ⟨le_rfl, ha.le⟩))) hab
  refine ⟨b - origin, ?_, ?_, ?_⟩
  · simp only [div_one] at hab
    linarith
  · simp only [zero_div, add_zero] at hb0
    linarith
  · simpa only [div_one, add_sub_cancel] using hfree

/-- A closed scalar ceiling on the strict history also holds at its
included first point, by the actual ordinary right slab; pp. 402-405. -/
theorem component_cylinder_scalar_le_at_left
    (P : M47Predecessors.{u})
    (e : SurgeryFlowCylinder F C origin 1 (Icc a 0) U) (ha : a < 0)
    {x : C.carrier} (hx : x ∈ U) {H : ℝ}
    (hbound : ∀ s : ℝ, ∀ hs : s ∈ Ioc a 0,
      (F.connection (origin + s / 1)).scalarCurvature
        (e.forward s ⟨hs.1.le, hs.2⟩ x) ≤ H) :
    (F.connection (origin + a / 1)).scalarCurvature
      (e.forward a ⟨le_rfl, ha.le⟩ x) ≤ H := by
  obtain ⟨r, har, hr0, hfree⟩ := exists_component_right_slab e ha
  have haI : a ∈ Icc a 0 := ⟨le_rfl, ha.le⟩
  have hrI : r ∈ Icc a 0 := ⟨har.le, hr0.le⟩
  have hab : origin + a / 1 < origin + r / 1 := by
    simp only [div_one]
    linarith
  have hJ : Icc (origin + a / 1) (origin + r / 1) ⊆ F.time_domain :=
    F.time_domain_interval.out (e.time_subset (mem_image_of_mem _ haI))
      (e.time_subset (mem_image_of_mem _ hrI))
  have hVI : Icc a r ⊆ Icc a 0 := Icc_subset_Icc le_rfl hr0.le
  have hclock : MapsTo (fun s : ℝ => origin + s / 1) (Icc a r)
      (Icc (origin + a / 1) (origin + r / 1)) := by
    intro s hs
    simp only [div_one]
    constructor <;> linarith [hs.1, hs.2]
  let P44 : M44CapPersistencePredecessors.{u} := ⟨P.m04, P.m13.ordinary_flow⟩
  have hc := cylinderScalar_continuousOn_slab P44 e hx hab hJ hfree a haI
    ⟨le_rfl, hab.le⟩ hVI hclock
  have hlim : Tendsto (cylinderScalar e x) (𝓝[>] a) (𝓝 (cylinderScalar e x a)) :=
    ((hc a ⟨le_rfl, har.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE har)).mono
      Ioi_subset_Ici_self
  have h := le_of_tendsto hlim (by
    filter_upwards [Ioc_mem_nhdsGT har] with s hs
    rw [cylinderScalar_of_mem e x s ⟨hs.1.le, hs.2.trans hr0.le⟩]
    exact hbound s ⟨hs.1, hs.2.trans hr0.le⟩)
  simpa only [cylinderScalar_of_mem e x a haI] using h

/-- A closed quadratic ceiling on the strict history persists at the
first included time on the same point and tangent; Lemma 3.15, p. 42. -/
theorem component_cylinder_quadratic_le_at_left
    (e : SurgeryFlowCylinder F C origin 1 (Icc a 0) U)
    (hU : IsOpen U) (ha : a < 0) {x : C.carrier} (hx : x ∈ U)
    (v : TangentSpace (𝓡 3) x) {H : ℝ}
    (hbound : ∀ s : ℝ, ∀ hs : s ∈ Ioc a 0,
      e.pullbackInner s ⟨hs.1.le, hs.2⟩ x v v ≤ H) :
    e.pullbackInner a ⟨le_rfl, ha.le⟩ x v v ≤ H := by
  obtain ⟨r, har, hr0, hfree⟩ := exists_component_right_slab e ha
  have haI : a ∈ Icc a 0 := ⟨le_rfl, ha.le⟩
  have hrI : r ∈ Icc a 0 := ⟨har.le, hr0.le⟩
  have hab : origin + a / 1 < origin + r / 1 := by
    simp only [div_one]
    linarith
  have hJ : Icc (origin + a / 1) (origin + r / 1) ⊆ F.time_domain :=
    F.time_domain_interval.out (e.time_subset (mem_image_of_mem _ haI))
      (e.time_subset (mem_image_of_mem _ hrI))
  let S := F.regular_slabs _ _ hab hJ hfree
  let f := (S.identify ⟨origin + a / 1, ⟨le_rfl, hab.le⟩⟩).symm ∘ e.forward a haI
  let V := mfderiv (𝓡 3) (𝓡 3) f x v
  have hcMetric : ContinuousOn (fun t => (S.flow.metric t).inner (f x) V V)
      (Icc (origin + a / 1) (origin + r / 1)) := by
    intro t ht
    exact (S.flow.equation t ht (f x) V V).continuousWithinAt
  have hclock : MapsTo (fun s : ℝ => origin + s / 1) (Icc a r)
      (Icc (origin + a / 1) (origin + r / 1)) := by
    intro s hs
    simp only [div_one]
    constructor <;> linarith [hs.1, hs.2]
  have hc : ContinuousOn (cylinderQuadratic e x v) (Icc a r) := by
    apply (hcMetric.comp (by fun_prop : ContinuousOn
      (fun s : ℝ => origin + s / 1) (Icc a r)) hclock).congr
    intro s hs
    exact cylinderQuadratic_eq_slab e hU hx v hab hJ hfree a s haI
      ⟨hs.1, hs.2.trans hr0.le⟩ ⟨le_rfl, hab.le⟩ (hclock hs)
  have hlim : Tendsto (cylinderQuadratic e x v) (𝓝[>] a) (𝓝 (cylinderQuadratic e x v a)) :=
    ((hc a ⟨le_rfl, har.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE har)).mono
      Ioi_subset_Ici_self
  have h := le_of_tendsto hlim (by
    filter_upwards [Ioc_mem_nhdsGT har] with s hs
    change cylinderQuadratic e x v s ≤ H
    classical
    simp only [cylinderQuadratic, dif_pos (show s ∈ Icc a 0 from
      ⟨hs.1.le, hs.2.trans hr0.le⟩)]
    exact hbound s ⟨hs.1, hs.2.trans hr0.le⟩)
  classical
  simpa only [cylinderQuadratic, dif_pos haI] using h

end PoincareMT.M47
