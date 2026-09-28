import PoincareConjecture.Proofs.M47.ComponentEstimateGauge
import PoincareConjecture.Proofs.M33.RegularHistory
import PoincareConjecture.Proofs.M33.SurgeryCylinderRestriction
import PoincareConjecture.Proofs.M33.GuardedCylinders
import PoincareConjecture.Proofs.M12.Geometry.Riemannian.Curvature.LocalIsometryInvariants
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.LocalIsometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

theorem exists_component_strict_ordinary_history
    (P : M47Predecessors.{u}) {F : SurgeryFlowData.{u}}
    {C : GeneralizedSliceCarrier.{u}} {origin a : ℝ} (ha : a < 0)
    (U : TopologicalSpace.Opens C.carrier) (hne : (U : Set C.carrier).Nonempty)
    (e : SurgeryFlowCylinder F C origin 1 (Icc a 0) U) :
    ∃ G : RicciFlow 3 U (Ioc (origin + a) origin),
      ∀ (s : ℝ) (hs : s ∈ Ioc a 0) (x : U),
        (∀ v w : TangentSpace (𝓡 3) x,
          (F.metric (origin + s / 1)).inner (e.forward s ⟨hs.1.le, hs.2⟩ x.val)
            (mfderiv (𝓡 3) (𝓡 3)
              (fun y : U => e.forward s ⟨hs.1.le, hs.2⟩ y.val) x v)
            (mfderiv (𝓡 3) (𝓡 3)
              (fun y : U => e.forward s ⟨hs.1.le, hs.2⟩ y.val) x w) =
                (G.metric (origin + s / 1)).inner x v w) ∧
        (G.connection (origin + s / 1)).scalarCurvature x =
          (F.connection (origin + s / 1)).scalarCurvature
            (e.forward s ⟨hs.1.le, hs.2⟩ x.val) ∧
        (G.connection (origin + s / 1)).curvatureTensorNorm x =
          (F.connection (origin + s / 1)).curvatureTensorNorm
            (e.forward s ⟨hs.1.le, hs.2⟩ x.val) := by
  have haI : a ∈ Icc a 0 := ⟨le_rfl, ha.le⟩
  have h0I : 0 ∈ Icc a 0 := ⟨ha.le, le_rfl⟩
  have hstart : origin + a ∈ F.time_domain := by
    simpa only [div_one] using e.time_subset (mem_image_of_mem _ haI)
  have hterminal : origin ∈ F.time_domain := by
    simpa only [zero_div, add_zero] using e.time_subset (mem_image_of_mem _ h0I)
  have horigin : 0 < origin := by
    have hnonnegative := F.time_domain_nonnegative hstart
    change 0 ≤ origin + a at hnonnegative
    linarith
  obtain ⟨x0, _hx0⟩ := hne
  have hnonempty : Nonempty (F.slice origin).carrier := by
    have h : Nonempty (F.slice (origin + 0 / 1)).carrier := ⟨e.forward 0 h0I x0⟩
    simpa only [zero_div, add_zero] using h
  let W := F.closedRegularHistoryWindow origin horigin hterminal hnonempty
  obtain ⟨H⟩ := P.regular_history F W
  let J : SpacetimeInterval := {
    domain := Ioc a 0
    ordConnected := ordConnected_Ioc
    nontrivial := ⟨a / 2, ⟨by linarith, by linarith⟩,
      0, ⟨ha, le_rfl⟩, by linarith⟩
  }
  let short := e.restrict Ioc_subset_Icc_self J.ordConnected (Subset.refl (U : Set C.carrier))
  have htime : ∀ s ∈ J.domain, origin + s / 1 ∈ W.interval := by
    intro s hs
    have ht := e.time_subset (mem_image_of_mem _ (Ioc_subset_Icc_self hs))
    exact ⟨F.time_domain_nonnegative ht, by
      have h := hs.2
      change origin + s / 1 ≤ origin
      simp only [div_one]
      linarith⟩
  have hregular : ∀ s hs, short.forward s hs '' (U : Set C.carrier) ⊆
      m33RegularRegion F (origin + s / 1) := by
    intro s hs
    exact e.regular_image_of_earlier (Ioc_subset_Icc_self hs) ⟨a, haI, hs.1⟩
  obtain ⟨G0, hmetric⟩ := exists_component_regular_cylinder_ordinary P H short htime hregular
  have hsub : Ioc (origin + a) origin ⊆
      (fun s : ℝ => origin + s / 1) '' J.domain := by
    intro t ht
    refine ⟨t - origin, ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
    simp only [div_one, add_sub_cancel]
  let G : RicciFlow 3 U (Ioc (origin + a) origin) := {
    metric := G0.metric
    connection := G0.connection
    interval := ordConnected_Ioc
    nontrivial := ⟨origin + a / 2, ⟨by linarith, by linarith⟩,
      origin, ⟨by linarith, le_rfl⟩, by linarith⟩
    smooth := G0.smooth.mono (Set.prod_mono hsub Subset.rfl)
    equation := fun t ht x v w => (G0.equation t (hsub ht) x v w).mono hsub
  }
  refine ⟨G, ?_⟩
  intro s hs x
  have hf : ContMDiff (𝓡 3) (𝓡 3) ∞
      (fun y : U => e.forward s ⟨hs.1.le, hs.2⟩ y.val) := by
    intro y
    exact ((e.forward_smooth s ⟨hs.1.le, hs.2⟩ y.val y.property).contMDiffAt
      (U.isOpen.mem_nhds y.property)).comp y (contMDiff_subtype_val (n := ∞) y)
  have hm : ∀ y : U, ∀ v w : TangentSpace (𝓡 3) y,
      (G.metric (origin + s / 1)).inner y v w =
        (F.metric (origin + s / 1)).inner (e.forward s ⟨hs.1.le, hs.2⟩ y.val)
          (mfderiv (𝓡 3) (𝓡 3)
            (fun z : U => e.forward s ⟨hs.1.le, hs.2⟩ z.val) y v)
          (mfderiv (𝓡 3) (𝓡 3)
            (fun z : U => e.forward s ⟨hs.1.le, hs.2⟩ z.val) y w) :=
    fun y v w => (hmetric s hs y v w).symm
  refine ⟨fun v w => (hm x v w).symm, ?_, ?_⟩
  · exact (G.connection (origin + s / 1)).scalarCurvature_eq_of_local_isometry
      (F.connection (origin + s / 1)) isOpen_univ hf.contMDiffOn
      (fun y _hy => hm y) (mem_univ x)
  · exact (G.connection (origin + s / 1)).curvatureTensorNorm_eq_of_local_isometry
      (F.connection (origin + s / 1)) isOpen_univ hf.contMDiffOn
      (fun y _hy => hm y) (mem_univ x)

end PoincareConjecture.M47
