import PoincareConjecture.Proofs.M47.ComponentHistory
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceNormalization
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_AmbientBalls
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_InitialConfinement

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M47

variable {g₀ : StandardInitialMetric} {K : MetricSurgeryConstants}
  {P : SurgeryParameters} {slice : ℝ → GeneralizedSliceCarrier.{u}}
  {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {T : ℝ}

theorem localResult_range_subset_component
    (E : SurgeryEventData g₀ K P slice metric T) (i : Fin E.cap_count) :
    range (E.local_embed i) ⊆ connectedComponent (E.caps i).tip := by
  let e : (E.local_result i).output.carrier ≃ₜ StandardCapSpace :=
    (Classical.choice (E.local_result i).open_ball_model).trans Homeomorph.ulift
  let : ConnectedSpace (E.local_result i).output.carrier :=
    e.connectedSpace_iff.mpr inferInstance
  rw [← E.local_tip i]
  exact (isPreconnected_range (E.local_embed_smooth i).continuous).subset_connectedComponent
    (mem_range_self (E.local_result i).tip)

theorem cap_subset_tip_component
    (E : SurgeryEventData g₀ K P slice metric T) (i : Fin E.cap_count) :
    (E.caps i).carrier ⊆ connectedComponent (E.caps i).tip := by
  rw [← E.local_cap_image i]
  exact (image_subset_range _ _).trans (localResult_range_subset_component E i)

theorem localResult_not_compact
    (E : SurgeryEventData g₀ K P slice metric T) (i : Fin E.cap_count) :
    ¬ IsCompact (univ : Set (E.local_result i).output.carrier) := by
  intro hcompact
  let e : (E.local_result i).output.carrier ≃ₜ StandardCapSpace :=
    (Classical.choice (E.local_result i).open_ball_model).trans Homeomorph.ulift
  have h := hcompact.image e.continuous
  rw [image_univ, e.surjective.range_eq] at h
  exact noncompact_univ StandardCapSpace h

theorem localResult_component_not_subset_ball
    (E : SurgeryEventData g₀ K P slice metric T) (i : Fin E.cap_count)
    {r : ℝ} (hr : 0 < r)
    (hcompact : IsCompact (closure ((E.local_result i).metric.ball
      (E.local_result i).tip r))) :
    ¬ connectedComponent (E.caps i).tip ⊆ (metric T).ball (E.caps i).tip r := by
  intro hsub
  let : Nonempty (E.local_result i).output.carrier := ⟨(E.local_result i).tip⟩
  have himage := (E.local_result i).metric.image_ball_of_precompact_pullback (metric T)
    (E.local_embed_smooth i) (E.local_embed_injective i) (E.local_metric i)
    (E.local_result i).tip hr hcompact
  rw [E.local_tip i] at himage
  have hall : (E.local_result i).metric.ball (E.local_result i).tip r = univ := by
    apply eq_univ_of_forall
    intro y
    have hy := hsub (localResult_range_subset_component E i (mem_range_self y))
    rw [← himage] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    exact (E.local_embed_injective i hzy) ▸ hz
  rw [hall, closure_univ] at hcompact
  exact localResult_not_compact E i hcompact

theorem component_disjoint_cap_of_precompact_ball
    (E : SurgeryEventData g₀ K P slice metric T) (i : Fin E.cap_count)
    (x : (slice T).carrier) {r : ℝ} (hr : 0 < r)
    (hcompact : IsCompact (closure ((E.local_result i).metric.ball
      (E.local_result i).tip r)))
    (hdiam : intrinsicDiameter (metric T) (connectedComponent x) < ENNReal.ofReal r) :
    Disjoint (connectedComponent x) (E.caps i).carrier := by
  apply Set.disjoint_left.2
  intro y hy hcap
  have htip := cap_subset_tip_component E i hcap
  have hcc : connectedComponent x = connectedComponent (E.caps i).tip :=
    (connectedComponent_eq hy).trans (connectedComponent_eq htip).symm
  apply localResult_component_not_subset_ball E i hr hcompact
  intro z hz
  rw [← hcc] at hz
  have htipx : (E.caps i).tip ∈ connectedComponent x := by
    rw [hcc]
    exact mem_connectedComponent
  exact ((edist_le_intrinsicEDist (connectedComponent x) (E.caps i).tip z).trans
    (intrinsicEDist_le_intrinsicDiameter htipx hz)).trans_lt hdiam

theorem component_disjoint_cap_of_comparison
    (E : SurgeryEventData g₀ K P slice metric T) (i : Fin E.cap_count)
    (x : (slice T).carrier) {eta rho : ℝ}
    (Q : SurgeryCapClose g₀ (E.local_result i).output (E.local_result i).metric
      (E.local_result i).tip (E.necks i).neck.scale eta)
    (heta : eta < 1) (hrho : 0 < rho) (hbuffer : rho < eta⁻¹)
    (hdiam : intrinsicDiameter (metric T) (connectedComponent x) <
      ENNReal.ofReal (Real.sqrt ((E.necks i).neck.scale ^ 2 * (1 - eta)) * rho)) :
    Disjoint (connectedComponent x) (E.caps i).carrier := by
  apply component_disjoint_cap_of_precompact_ball E i x
    (mul_pos (Real.sqrt_pos.mpr (mul_pos (sq_pos_of_pos Q.scale_pos)
      (sub_pos.mpr heta))) hrho)
    (Q.isCompact_closure_ball_of_buffer heta hrho hbuffer) hdiam

end PoincareConjecture.M47
