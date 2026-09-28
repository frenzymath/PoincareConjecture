import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Branch
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M33RegularHistoryRealization

variable {G : GeneralizedRicciFlowData.{u}} {F : SurgeryFlowData.{u}}
  {C : GeneralizedSliceCarrier.{u}} {origin scale : ℝ} {J : Set ℝ} {U : Set C.carrier}
  (h : M33RegularHistoryRealization G F)

theorem cylinder_slab_compatibility
    (e : GeneralizedFlowCylinder G C origin scale J U) (hJ : J.OrdConnected)
    (htime : ∀ s ∈ J, origin + s / scale ∈ G.interval)
    (a b : ℝ) (hab : a < b) (hJab : Icc a b ⊆ F.time_domain)
    (hfree : Disjoint F.surgery_times (Ioc a b))
    (s : ℝ) (hs : s ∈ J) (t : ℝ) (ht : t ∈ J)
    (hs' : origin + s / scale ∈ Icc a b) (ht' : origin + t / scale ∈ Icc a b)
    (x : C.carrier) (hx : x ∈ U) :
    (F.regular_slabs a b hab hJab hfree).transport
      ⟨origin + s / scale, hs'⟩ ⟨origin + t / scale, ht'⟩
      (h.forward (origin + s / scale) (htime s hs) (e.forward s hs x)) =
        h.forward (origin + t / scale) (htime t ht) (e.forward t ht x) := by
  let A := F.regular_slabs a b hab hJab hfree
  let K := J ∩ (fun r => origin + r / scale) ⁻¹' Icc a b
  let f : K → (F.slice a).carrier := fun q =>
    (A.identify ⟨origin + q.val / scale, q.property.2⟩).symm
      (h.forward (origin + q.val / scale) (htime q.val q.property.1)
        (e.forward q.val q.property.1 x))
  have hK : K.OrdConnected :=
    hJ.inter (ordConnected_Icc.preimage_mono
      (fun r v hrv => add_le_add le_rfl (div_le_div_of_nonneg_right hrv e.scale_pos.le)))
  have hf : IsLocallyConstant f := by
    apply (IsLocallyConstant.iff_eventually_eq f).mpr
    intro q
    obtain ⟨c, y, d, hd, hlocal⟩ := e.vertical_compatibility q.val q.property.1 x hx
    obtain ⟨hqc, hqeq⟩ := hlocal q.val q.property.1 (by simpa using hd)
    have hball : Subtype.val ⁻¹' Metric.ball q.val d ∈ nhds q :=
      (Metric.isOpen_ball.preimage continuous_subtype_val).mem_nhds
        (Metric.mem_ball_self hd)
    apply Filter.mem_of_superset hball
    intro r hr
    obtain ⟨hrc, hreq⟩ := hlocal r.val r.property.1 (by
      simpa only [mem_preimage, Metric.mem_ball, Real.dist_eq] using hr)
    have htransport : A.transport
        ⟨origin + q.val / scale, q.property.2⟩ ⟨origin + r.val / scale, r.property.2⟩
        (h.forward (origin + q.val / scale) (htime q.val q.property.1)
          (e.forward q.val q.property.1 x)) =
        h.forward (origin + r.val / scale) (htime r.val r.property.1)
          (e.forward r.val r.property.1 x) := by
      rw [hqeq, hreq]
      exact h.slab_compatibility c a b hab hJab hfree
        (origin + q.val / scale) (origin + r.val / scale)
        q.property.2 r.property.2 hqc hrc y
    have hcoords := congrArg
      ((A.identify ⟨origin + r.val / scale, r.property.2⟩).symm) htransport
    change f r = f q
    simpa only [f, SurgeryRegularSlab.transport, Diffeomorph.symm_apply_apply] using hcoords.symm
  let : PreconnectedSpace K := Subtype.preconnectedSpace hK.isPreconnected
  have heq := hf.apply_eq_of_preconnectedSpace (⟨s, hs, hs'⟩ : K) (⟨t, ht, ht'⟩ : K)
  change A.identify ⟨origin + t / scale, ht'⟩ (f ⟨s, hs, hs'⟩) = _
  rw [heq]
  exact (A.identify ⟨origin + t / scale, ht'⟩).apply_symm_apply _

end PoincareConjecture.M33RegularHistoryRealization
