import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Coordinates.Control
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.CompactEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 8

open Set Filter Manifold
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}

theorem exists_uniform_coordinate_metric_jet_tail_on_compact
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    (q : M) {K : Set (EuclideanSpace ℝ (Fin 3))} (hK : IsCompact K)
    (htarget : K ⊆ (extChartAt (𝓡 3) q).target)
    (hreg : (extChartAt (𝓡 3) q).symm '' K ⊆ H.reference.regularLimitSet) :
    ∃ s : ℝ, H.reference.tMinus < s ∧ s < T ∧
      ∀ m : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Ico s T, ∀ z ∈ K,
        ‖iteratedFDeriv ℝ m ((H.reference.flow.metric t).pullbackCoefficients
          (extChartAt (𝓡 3) q).symm) z‖ ≤ B := by
  let c := extChartAt (𝓡 3) q
  have himage : IsCompact (c.symm '' K) :=
    hK.image_of_continuousOn ((continuousOn_extChartAt_symm q).mono htarget)
  obtain ⟨s, hs, hsT, hder⟩ :=
    H.exists_uniform_curvature_derivative_tail_on_compact P04 himage hreg
  have hcont := ((H.reference.flow.metric s).contDiffOn_chartCoefficients q).continuousOn.mono
    htarget
  have hpos : ∀ z ∈ K, ∀ v : EuclideanSpace ℝ (Fin 3), v ≠ 0 →
      0 < (H.reference.flow.metric s).pullbackCoefficients c.symm z v v := by
    intro z hz v hv
    apply (H.reference.flow.metric s).pos
    intro hzero
    obtain ⟨e, he⟩ :=
      Poincare.Manifold.VectorField.isInvertible_mfderiv_extChartAt_symm (htarget hz)
    apply hv
    apply e.injective
    rw [map_zero]
    change e.toContinuousLinearMap v = 0
    rw [he]
    exact hzero
  obtain ⟨a, ha, hlow⟩ := exists_uniform_bilinear_lower_bound hK hcont hpos
  obtain ⟨b, hhigh⟩ := hK.exists_bound_of_continuousOn hcont
  let b' := max b 0
  have hb' : 0 ≤ b' := le_max_right _ _
  have hupper : ∀ z ∈ K, ∀ v : EuclideanSpace ℝ (Fin 3),
      (H.reference.flow.metric s).pullbackCoefficients c.symm z v v ≤ b' * ‖v‖ ^ 2 := by
    intro z hz v
    calc
      _ ≤ ‖(H.reference.flow.metric s).pullbackCoefficients c.symm z v v‖ := le_abs_self _
      _ ≤ ‖(H.reference.flow.metric s).pullbackCoefficients c.symm z‖ * ‖v‖ * ‖v‖ :=
        ContinuousLinearMap.le_opNorm₂ _ v v
      _ ≤ b' * ‖v‖ ^ 2 := by
        rw [pow_two, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right ((hhigh z hz).trans (le_max_left _ _))
            (norm_nonneg v)) (norm_nonneg v)
  obtain ⟨R, hR, hRm⟩ := hder 0
  let L := Real.exp (-2 * (3 : ℝ) * R * (T - s))
  let U := Real.exp (2 * (3 : ℝ) * R * (T - s))
  have hL : 0 < L := Real.exp_pos _
  have hU : 0 < U := Real.exp_pos _
  have hell : ∀ t ∈ Ico s T, ∀ z ∈ K, ∀ v,
      (L * a) * ‖v‖ ^ 2 ≤ (H.reference.flow.metric t).pullbackCoefficients c.symm z v v ∧
      (H.reference.flow.metric t).pullbackCoefficients c.symm z v v ≤ (U * b') * ‖v‖ ^ 2 := by
    intro t ht z hz v
    let w := mfderiv (𝓡 3) (𝓡 3) c.symm z v
    have hcurv : ∀ τ ∈ Ico s T,
        (H.reference.flow.connection τ).curvatureTensorNorm (c.symm z) ≤ R := by
      intro τ hτ
      rw [← P04.curvature_norm_zero 3 M (H.reference.flow.metric τ)
        (H.reference.flow.connection τ)]
      exact hRm τ hτ (c.symm z) (mem_image_of_mem c.symm hz)
    have htime := RicciFlowAnalysis.metric_diagonal_bounds_on_tail
      H.reference.flow hs.le hsT hR.le (c.symm z) hcurv w ht
    constructor
    · calc
        _ = L * (a * ‖v‖ ^ 2) := by ring
        _ ≤ L * (H.reference.flow.metric s).inner (c.symm z) w w :=
          mul_le_mul_of_nonneg_left (hlow z hz v) hL.le
        _ ≤ _ := htime.1
    · calc
        _ ≤ U * (H.reference.flow.metric s).inner (c.symm z) w w := htime.2
        _ ≤ U * (b' * ‖v‖ ^ 2) := mul_le_mul_of_nonneg_left (hupper z hz v) hU.le
        _ = _ := by ring
  have hdom : (fun z : ℝ => z + s) '' Ioo (H.reference.tMinus - s) (T - s) ⊆
      Ico H.reference.tMinus T := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have hzero : (0 : ℝ) ∈ Ioo (H.reference.tMinus - s) (T - s) :=
    ⟨by linarith, by linarith⟩
  have hmid : (T - s) / 2 ∈ Ioo (H.reference.tMinus - s) (T - s) :=
    ⟨by linarith, by linarith⟩
  let G := H.reference.flow.translate s hdom ordConnected_Ioo
    ⟨0, hzero, (T - s) / 2, hmid, by linarith⟩
  have htime : Ico (0 : ℝ) (T - s) ⊆ Ioo (H.reference.tMinus - s) (T - s) := by
    intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩
  have hshift {t : ℝ} (ht : t ∈ Ico 0 (T - s)) : t + s ∈ Ico s T :=
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hbounds := SingularRegularLimit.uniform_spatial_metric_jet_bounds G isOpen_Ioo
    (sub_pos.mpr hsT) htime (isOpen_extChartAt_target q)
    (contMDiffOn_extChartAt_symm q)
    (fun _ hz => Poincare.Manifold.VectorField.isInvertible_mfderiv_extChartAt_symm hz)
    hK htarget (mul_pos hL ha) (mul_nonneg hU.le hb')
    (fun t ht z hz v => hell (t + s) (hshift ht) z hz v)
    (fun k => by
      obtain ⟨C, _, hC⟩ := hder k
      exact ⟨C, fun t ht z hz => hC (t + s) (hshift ht) (c.symm z)
        (mem_image_of_mem c.symm hz)⟩)
  refine ⟨s, hs, hsT, ?_⟩
  intro m
  obtain ⟨B, hB, hbound⟩ := hbounds m
  refine ⟨B, hB, ?_⟩
  intro t ht z hz
  have h := hbound (t - s) ⟨by linarith [ht.1], by linarith [ht.2]⟩ z hz
  change ‖iteratedFDeriv ℝ m
    ((H.reference.flow.metric (t - s + s)).pullbackCoefficients c.symm) z‖ ≤ B at h
  simpa only [sub_add_cancel] using h

end PoincareConjecture.SingularTimeAssumptions
