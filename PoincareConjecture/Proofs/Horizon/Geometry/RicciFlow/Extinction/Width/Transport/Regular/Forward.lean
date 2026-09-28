import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.Transport.Regular.Neighborhoods
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.Transport.Slice.Metric

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable
    {g₀ : StandardInitialMetric}
    {D : RepairedSurgeryFlowData.{u} g₀}
    {W : RepairedEventChildWitness D.flow}
    {T : ℝ} {P : RepairedComponentPath D.flow T W}
    {K : RepairedComparisonMapData D}
    {C : RepairedComparisonHomotopyData D K}
    {H : RepairedAncestryTransportInput D W P K C}
    {B : M59HigherBasepointTransportService}
    {A : RepairedAncestryTransportData D W P K C H B}
    {q : M59SphereQuotient}
    {hM61 : M61RawWidthCore.{u}}
    {hM64 : M64ComparisonTheory.{u}}
    {hM65 : M65DeformationTheory hM61 hM64}

theorem m67_slice_scalar_eq_actual
    (X : M67ChangingWidthPath D W P K C H B A q hM61 hM65)
    (s : Set.Icc (0 : ℝ) T) (x : (P.component s).carrier.carrier) :
    (X.slice s).connection.scalarCurvature x =
      (D.flow.connection s.1).scalarCurvature ((P.component s).inclusion x) := by
  apply (X.slice s).connection.scalarCurvature_eq_of_local_isometry
    (D.flow.connection s.1) isOpen_univ (P.component s).inclusion_smooth.contMDiffOn
    (fun y _ v w => ?_) (Set.mem_univ x)
  rw [← X.ambient_metric_eq s]
  exact ((X.slice s).metric_pullback y v w).symm

theorem m67_regular_scalar_left
    (X : M67ChangingWidthPath D W P K C H B A q hM61 hM65)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ T)
    (hJ : Disjoint D.flow.surgery_times (Set.Ioc a b))
    (x : (P.component ⟨a, ⟨ha, hab.le.trans hb⟩⟩).carrier.carrier) :
    ((X.regular_flow ha hab hb hJ).connection a).scalarCurvature x =
      (X.slice ⟨a, ⟨ha, hab.le.trans hb⟩⟩).connection.scalarCurvature x := by
  let s : Set.Icc (0 : ℝ) T := ⟨a, ⟨ha, hab.le.trans hb⟩⟩
  let slab := D.flow.regular_slabs a b hab
    (fun _u hu => P.time_subset ⟨ha.trans hu.1, hu.2.trans hb⟩) hJ
  let a' : Set.Icc a b := ⟨a, le_rfl, hab.le⟩
  have hscalar := (slab.flow.connection a).scalarCurvature_eq_of_local_isometry
    (D.flow.connection a) isOpen_univ (slab.identify a').contMDiff.contMDiffOn
    (fun y _ v w => (slab.metric_pullback a' y v w).symm)
    (Set.mem_univ ((P.component s).inclusion x))
  rw [slab.initial_identify] at hscalar
  exact (X.regular_flow_scalar_calibration ha hab hb hJ a' x).trans
    (hscalar.trans (m67_slice_scalar_eq_actual X s x).symm)

theorem m67_width_forward_difference
    (X : M67ChangingWidthPath D W P K C H B A q hM61 hM65)
    (s : Set.Icc (0 : ℝ) T) (hs : s.1 < T)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ t : Set.Icc (0 : ℝ) T, s.1 < t.1 → t.1 < s.1 + delta →
        (X.width t - X.width s) / (t.1 - s.1) ≤
          -2 * Real.pi - X.scalar_infimum s / 2 * X.width s + epsilon := by
  obtain ⟨b, hsb, hb, hJ⟩ := m67_exists_right_regular_interval P s hs
  obtain ⟨J⟩ := X.regular_piece s.2.1 hsb hb hJ
  let s' : Set.Icc s.1 b := ⟨s.1, le_rfl, hsb.le⟩
  have hscalar : flowScalarCurvatureInfimum J.input.flow s.1 = X.scalar_infimum s := by
    rw [X.scalar_infimum_eq, J.input_flow_eq]
    unfold flowScalarCurvatureInfimum
    congr 2
    funext x
    exact m67_regular_scalar_left X s.2.1 hsb hb hJ x
  obtain ⟨delta, hd, hbound⟩ :=
    J.conclusion.forward_difference_bound s' hsb epsilon hepsilon
  refine ⟨min delta (b - s.1), lt_min hd (sub_pos.mpr hsb), ?_⟩
  intro t hst ht
  have htb : t.1 ≤ b := by
    have := min_le_right delta (b - s.1)
    linarith
  let t' : Set.Icc s.1 b := ⟨t.1, hst.le, htb⟩
  have htnear : t.1 < s.1 + delta := by
    have := min_le_left delta (b - s.1)
    linarith
  have h := hbound t' hst htnear
  have hs_eq : J.interval s' = s := Subtype.ext (J.interval_time s')
  have ht_eq : J.interval t' = t := Subtype.ext (J.interval_time t')
  rw [← J.width_agreement t', ← J.width_agreement s', ht_eq, hs_eq] at h
  exact hscalar ▸ h

end PoincareConjecture
