import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.PersistenceGeometry
import PoincareLib.Geometry.RicciFlow.Surgery.Continuation.Construction.RegularHistory
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Topology.ConnectedFrontier
import PoincareLib.Geometry.RicciFlow.Compactness.GeometricLimit.BoundaryCoverage

/-!
# Stopping times and the connectedness step of Claim 16.10

Morgan--Tian, pp. 374-375: local finiteness selects a first later surgery
on each compact physical interval. After the geometric neck-avoidance
argument, connectedness converts one lost line to whole-ball removal.
This file proves those two steps, keeping neck avoidance explicit.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareMT

/-- The actual preterminal image of a connected tracked region is
preconnected (Claim 16.10, p. 375). -/
theorem SurgeryFlowCylinder.preterminal_image_preconnected
    {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {origin scale : ℝ} {I : Set ℝ} {U : Set C.carrier}
    (e : SurgeryFlowCylinder F C origin scale I U) (hU : IsPreconnected U)
    {tPlus : ℝ} (hPlus : tPlus ∈ F.surgery_times)
    [Nonempty (F.slice tPlus).carrier] (s : ℝ) (hs : s ∈ I)
    (ht : origin + s / scale ∈ Ico (F.event tPlus hPlus).tMinus tPlus) :
    IsPreconnected ((fun x => ((F.event tPlus hPlus).pre_identify
      ⟨origin + s / scale, ht⟩).symm (e.forward s hs x)) '' U) := by
  have hpre := ((F.event tPlus hPlus).pre_identify
    ⟨origin + s / scale, ht⟩).symm.contMDiff.continuous
  exact hU.image _ (hpre.comp_continuousOn (e.forward_smooth s hs).continuousOn)

/-- The tracked metric ball in Proposition 16.5 has a connected image
in the actual preterminal carrier, without a completeness assumption. -/
theorem SurgeryFlowCylinder.preterminal_ball_preconnected
    {F : SurgeryFlowData.{u}} {origin scale : ℝ} {I : Set ℝ}
    (p : (F.slice origin).carrier) (r : ℝ)
    (e : SurgeryFlowCylinder F (F.slice origin) origin scale I
      ((F.metric origin).ball p r))
    {tPlus : ℝ} (hPlus : tPlus ∈ F.surgery_times)
    [Nonempty (F.slice tPlus).carrier] (s : ℝ) (hs : s ∈ I)
    (ht : origin + s / scale ∈ Ico (F.event tPlus hPlus).tMinus tPlus) :
    IsPreconnected ((fun x => ((F.event tPlus hPlus).pre_identify
      ⟨origin + s / scale, ht⟩).symm (e.forward s hs x)) ''
        (F.metric origin).ball p r) :=
  e.preterminal_image_preconnected ((F.metric origin).isPreconnected_ball p r)
    hPlus s hs ht

/-- On an actual compact time interval, a first later surgery exists
unless the interval is surgery free (Proposition 16.5, p. 374). -/
theorem SurgeryFlowData.first_surgery_or_free (F : SurgeryFlowData.{u})
    {a b : ℝ} (hJ : Icc a b ⊆ F.time_domain) :
    Disjoint F.surgery_times (Ioc a b) ∨
      ∃ tPlus ∈ F.surgery_times, tPlus ∈ Ioc a b ∧
        Disjoint F.surgery_times (Ioo a tPlus) := by
  classical
  by_cases hfree : Disjoint F.surgery_times (Ioc a b)
  · exact Or.inl hfree
  · right
    have hfinite : (F.surgery_times ∩ Ioc a b).Finite :=
      (F.surgery_times_finite_on_compact isCompact_Icc hJ).subset
        (inter_subset_inter_right _ Ioc_subset_Icc_self)
    have hnonempty : (F.surgery_times ∩ Ioc a b).Nonempty :=
      not_disjoint_iff_nonempty_inter.mp hfree
    obtain ⟨tPlus, htPlus, hminimal⟩ :=
      Set.exists_min_image _ (fun t : ℝ => t) hfinite hnonempty
    refine ⟨tPlus, htPlus.1, htPlus.2, Set.disjoint_left.mpr ?_⟩
    intro s hs hsI
    exact (not_lt_of_ge (hminimal s ⟨hs, hsI.1, hsI.2.le.trans htPlus.2.2⟩)) hsI.2

/-- The connectedness conclusion of Claim 16.10, p. 375, on the actual
preterminal carrier. The union of central spheres is the supplied frontier. -/
theorem SurgeryEventData.all_lost_of_avoids_necks
    {g₀ : StandardInitialMetric} {K : MetricSurgeryConstants} {P : SurgeryParameters}
    {slice : ℝ → GeneralizedSliceCarrier.{u}}
    {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {T : ℝ}
    (E : SurgeryEventData g₀ K P slice metric T)
    {U : Set (slice E.tMinus).carrier} (hU : IsPreconnected U)
    (havoid : ∀ i, Disjoint U
      (E.limit_identify.inverse '' (E.necks i).neck.central_sphere))
    (hlost : ∃ x ∈ U, x ∉ interior E.retained_pre) :
    U ⊆ (interior E.retained_pre)ᶜ := by
  apply hU.subset_compl_interior_of_disjoint_frontier _ hlost
  rw [E.pre_boundary]
  exact disjoint_iUnion_right.mpr havoid

/-- Assemble actual late preterminal whole-ball removal after the
connectedness step of Claim 16.10, p. 375. -/
theorem SurgeryFlowCylinder.disappears_of_late_neck_avoidance
    {F : SurgeryFlowData.{u}} {origin scale : ℝ} {I : Set ℝ}
    {U : Set (F.slice origin).carrier}
    (e : SurgeryFlowCylinder F (F.slice origin) origin scale I U)
    {tPlus : ℝ} (hPlus : tPlus ∈ F.surgery_times)
    [Nonempty (F.slice tPlus).carrier]
    (hinitial : ∀ h x, x ∈ U → HEq (e.forward 0 h x) x)
    {s0 : ℝ} (hs0 : s0 ∈ I)
    (hgeometry : ∀ s (hs : s ∈ I), s0 ≤ s →
      ∀ ht : origin + s / scale ∈ Ico (F.event tPlus hPlus).tMinus tPlus,
      let V := (fun x => ((F.event tPlus hPlus).pre_identify
        ⟨origin + s / scale, ht⟩).symm (e.forward s hs x)) '' U
      IsPreconnected V ∧
        (∀ i, Disjoint V ((F.event tPlus hPlus).limit_identify.inverse ''
          ((F.event tPlus hPlus).necks i).neck.central_sphere)) ∧
        ∃ x ∈ V, x ∉ interior (F.event tPlus hPlus).retained_pre) :
    SurgeryBallDisappearsAt F e tPlus := by
  refine Or.inr ⟨hPlus, inferInstance, hinitial, s0, hs0, ?_⟩
  intro s hs hlate x hx ht
  obtain ⟨hconnected, havoid, hlost⟩ := hgeometry s hs hlate ht
  exact (F.event tPlus hPlus).all_lost_of_avoids_necks hconnected havoid hlost
    (Set.mem_image_of_mem _ hx)

end PoincareMT
