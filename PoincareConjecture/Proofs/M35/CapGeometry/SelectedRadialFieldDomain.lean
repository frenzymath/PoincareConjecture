import PoincareConjecture.Proofs.M35.CapGeometry.RetainedShapeValue
import PoincareConjecture.Proofs.M35.CapGeometry.RetainedUnitField
import PoincareConjecture.Proofs.M35.Thm12_28.CylinderCoordinates

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace PoincareConjecture.M35.OrdinaryRealization

open Uniqueness

local notation "V" => EuclideanSpace ℝ (Fin 3)

theorem selected_coordinate_smooth_invertible {J : Set ℝ}
    (F : RicciFlow 3 StandardCapSpace J)
    {C : GeneralizedSliceCarrier} {a Q : ℝ} {I : Set ℝ} {U : Set C.carrier}
    (e : GeneralizedFlowCylinder (generalizedFlow F) C a Q I U)
    (hU : IsOpen U) (hzero : (0 : ℝ) ∈ I) (htime : a + 0 / Q ∈ J)
    (coordinate : V → C.carrier) (hc : ContMDiff (𝓡 3) (𝓡 3) ∞ coordinate)
    (hi : ∀ z, (mfderiv (𝓡 3) (𝓡 3) coordinate z).IsInvertible)
    {z : V} (hz : coordinate z ∈ U) :
    let f : V → StandardCapSpace := fun y => (e.forward 0 hzero (coordinate y)).val
    ContMDiffAt (𝓡 3) (𝓡 3) ∞ f z ∧ (mfderiv (𝓡 3) (𝓡 3) f z).IsInvertible := by
  let psi := cylinderSpatialCoordinates F e hU 0 hzero htime
  let f : C.carrier → StandardCapSpace := fun y => (e.forward 0 hzero y).val
  have hf : ContMDiffAt (𝓡 3) (𝓡 3) ∞ f (coordinate z) :=
    psi.contMDiffOn_toFun.contMDiffAt (hU.mem_nhds hz)
  have hlocal : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ f (coordinate z) :=
    ⟨psi, hz, fun _ _ => rfl⟩
  have hfi : (mfderiv (𝓡 3) (𝓡 3) f (coordinate z)).IsInvertible :=
    ⟨hlocal.mfderivToContinuousLinearEquiv (by simp), rfl⟩
  refine ⟨hf.comp z (hc z), ?_⟩
  change (mfderiv (𝓡 3) (𝓡 3) (f ∘ coordinate) z).IsInvertible
  rw [mfderiv_comp z (hf.mdifferentiableAt (by simp))
    ((hc z).mdifferentiableAt (by simp))]
  exact hfi.comp (hi z)

theorem blowupSequence_coordinate_radial_domain
    (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (hd : Tendsto (fun k => ((E.flow.metric (t k)).edist 0 (x k)).toReal *
      Real.sqrt ((E.flow.connection (t k)).scalarCurvature (x k))) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤)) :
    letI : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
    letI : ChartedSpace V L.limit.carrier.carrier := L.limit.carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
    ∀ (coordinate : V → L.limit.sliceCarrier.carrier)
      (_hc : ContMDiff (𝓡 3) (𝓡 3) ∞ coordinate)
      (_hi : ∀ z, (mfderiv (𝓡 3) (𝓡 3) coordinate z).IsInvertible)
      (K : Set V) (_hK : IsCompact K),
      ∀ᶠ k in atTop,
        let Q := (blowupSequence P E t x ht hR).scale (L.subsequence k)
        let hQ := (blowupSequence P E t x ht hR).base_scalar_pos (L.subsequence k)
        let G := M13.scaleSmoothMetric (E.flow.metric (t (L.subsequence k))) Q hQ
        let f : V → StandardCapSpace := fun z => ((L.embedding k).forward 0
          ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ (coordinate z)).val
        ∀ z ∈ K,
          (∀ᶠ y in 𝓝 z, ContMDiffAt (𝓡 3) (𝓡 3) ∞ f y ∧
            (mfderiv (𝓡 3) (𝓡 3) f y).IsInvertible ∧ f y ≠ 0) ∧
          |axisWarpingSlope G ‖f z‖ / axisWarpingRadius G ‖f z‖| ≤ 1 := by
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : ChartedSpace V L.limit.carrier.carrier := L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  have : T3Space L.limit.sliceCarrier.carrier := L.limit.carrier.t3Space
  have : ConnectedSpace L.limit.sliceCarrier.carrier := L.limit.connectedSpace
  intro coordinate hc hi K hK
  let H := coordinate '' K
  have hH : IsCompact H := hK.image hc.continuous
  obtain ⟨j, hj⟩ := hH.elim_directed_cover L.exhaustion.space L.exhaustion.space_open
    (fun z _ => by rw [L.exhaustion.space_covers]; exact mem_univ z)
    (fun i j => ⟨max i j, L.exhaustion.space_increasing (le_max_left _ _),
      L.exhaustion.space_increasing (le_max_right _ _)⟩)
  let g : RiemannianMetric 3 L.limit.sliceCarrier.carrier := L.limit.flow.metric 0
  obtain ⟨B, hB⟩ := hH.exists_bound_of_continuousOn
    (g.continuous_toReal_edist L.limit.base).continuousOn
  let R := max B 0 + 1
  have hball : H ⊆ g.ball L.limit.base R := by
    intro y hy
    apply (ENNReal.lt_ofReal_iff_toReal_lt (g.edist_ne_top L.limit.base y)).mpr
    have h := hB y hy
    have hl : (g.edist L.limit.base y).toReal ≤ B :=
      (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using h)
    exact hl.trans_lt ((le_max_left B 0).trans_lt (lt_add_of_pos_right _ zero_lt_one))
  filter_upwards [eventually_ge_atTop j,
    blowupSequence_far_tip_radial_field_on_limit_ball P E t x ht hR hd L R 1 zero_lt_one,
    blowupSequence_far_tip_radial_shape_on_limit_ball P E t x ht hR hd L R 1 zero_lt_one]
    with k hk hfield hshape
  let Q := (blowupSequence P E t x ht hR).scale (L.subsequence k)
  have hQ : 0 < Q := (blowupSequence P E t x ht hR).base_scalar_pos (L.subsequence k)
  let G : RiemannianMetric 3 StandardCapSpace :=
    M13.scaleSmoothMetric (E.flow.metric (t (L.subsequence k))) Q hQ
  have hzero : (0 : ℝ) ∈ Icc (-L.exhaustion.time k) 0 :=
    ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩
  let f : V → StandardCapSpace := fun z => ((L.embedding k).forward 0 hzero (coordinate z)).val
  have htime := ((L.embedding k).forward 0 hzero L.limit.base).property
  change ∀ z ∈ K,
    (∀ᶠ y in 𝓝 z, ContMDiffAt (𝓡 3) (𝓡 3) ∞ f y ∧
      (mfderiv (𝓡 3) (𝓡 3) f y).IsInvertible ∧ f y ≠ 0) ∧
    |axisWarpingSlope G ‖f z‖ / axisWarpingRadius G ‖f z‖| ≤ 1
  intro z hz
  have hzH : coordinate z ∈ H := ⟨z, hz, rfl⟩
  have hzU : coordinate z ∈ L.exhaustion.space k := L.exhaustion.space_increasing hk (hj hzH)
  have hlocal {y : V} (hy : coordinate y ∈ L.exhaustion.space k) :=
    selected_coordinate_smooth_invertible E.flow.base.flow (L.embedding k)
      (L.exhaustion.space_open k) hzero htime coordinate hc hi hy
  have hne : f z ≠ 0 := (hfield (coordinate z) (hball hzH)).1
  have hnearU := (hc z).continuousAt.preimage_mem_nhds
    ((L.exhaustion.space_open k).mem_nhds hzU)
  have hnearZero := (hlocal hzU).1.continuousAt.preimage_mem_nhds
    (isOpen_compl_singleton.mem_nhds hne)
  refine ⟨?_, hshape (coordinate z) (hball hzH)⟩
  filter_upwards [hnearU, hnearZero] with y hy hny
  exact ⟨(hlocal hy).1, (hlocal hy).2, hny⟩

end PoincareConjecture.M35.OrdinaryRealization
