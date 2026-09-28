import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Component.TopologyTransport
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Component.RestrictedDistance
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Component.Distance
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Component.Curvature
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Component.RadiusExtrema

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}

theorem frequently_cComponent_intrinsicDiameter_bounds
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    (x : H.regularRegion P04)
    (hfreq : ∃ᶠ t in 𝓝[<] T, ∃ ht : t ∈ Ico H.reference.tMinus T,
      ∃ N : SingularCComponent (F.metric t) (F.connection t) H.constant,
        H.reference.forward t ht x ∈ N.carrier) :
    ∃ᶠ t in 𝓝[<] T,
      ENNReal.ofReal (H.constant⁻¹ * sSup (range
        (fun z : connectedComponent x => H.reference.scalar t z ^ (-1 / 2 : ℝ)))) <
          intrinsicDiameter ((H.terminalFlow P04).metric t) (connectedComponent x) ∧
      intrinsicDiameter ((H.terminalFlow P04).metric t) (connectedComponent x) <
        ENNReal.ofReal (H.constant * sInf (range
          (fun z : connectedComponent x => H.reference.scalar t z ^ (-1 / 2 : ℝ)))) := by
  obtain ⟨s, _, hsT, hcap⟩ := H.exists_late_cComponent_terminal_carrier P04 x
  have hsEv : ∀ᶠ t in 𝓝[<] T, s ≤ t :=
    (eventually_ge_nhds hsT).filter_mono nhdsWithin_le_nhds
  apply (hfreq.and_eventually hsEv).mono
  rintro t ⟨⟨ht, N, hxN⟩, hst⟩
  obtain ⟨_, hreg, hterminal, _⟩ := hcap t ht hst N hxN
  let N' := H.reference.referenceCComponent t ht N
  have hcarrier : N'.carrier = connectedComponent (x : M) :=
    H.reference.referenceCComponent_carrier t ht N hxN
  have hNU : N'.carrier ⊆ H.regularRegion P04 := by
    rw [hcarrier]
    exact hreg
  have hpre : (Subtype.val : H.regularRegion P04 → M) ⁻¹' N'.carrier =
      connectedComponent x := by
    rw [hcarrier]
    exact hterminal.symm
  have hdiam := SingularRegularLimit.intrinsicDiameter_restrictToOpen
    (H.regularRegion P04) (H.reference.flow.metric t) ((H.terminalFlow P04).metric t)
    (fun y v w => by
      rw [Poincare.Geometry.Manifold.RegularLevel.mfderiv_opens_subtypeVal]
      exact (H.terminalMetricFamily_inner_of_ne P04 ht.2.ne y v w).symm)
    N'.carrier hNU
  rw [hpre] at hdiam
  have hrange : range
      (fun z : connectedComponent x => H.reference.scalar t z ^ (-1 / 2 : ℝ)) =
      range (fun z : N'.carrier =>
        (H.reference.flow.connection t).scalarCurvature z ^ (-1 / 2 : ℝ)) := by
    ext a
    constructor
    · rintro ⟨z, rfl⟩
      have hz : (z.val : M) ∈ N'.carrier := by
        change z.val ∈ (Subtype.val : H.regularRegion P04 → M) ⁻¹' N'.carrier
        rw [hpre]
        exact z.property
      exact ⟨⟨z.val.val, hz⟩, rfl⟩
    · rintro ⟨z, rfl⟩
      have hz : (⟨z.val, hNU z.property⟩ : H.regularRegion P04) ∈ connectedComponent x := by
        rw [← hpre]
        exact z.property
      exact ⟨⟨⟨z.val, hNU z.property⟩, hz⟩, rfl⟩
  rw [hdiam, hrange]
  exact ⟨N'.diameter_lower, N'.diameter_upper⟩

private theorem strict_doubled_diameter_bounds
    {C a b : ℝ} (hC : 0 < C) (ha : 0 < a) (hb : 0 < b) {d : ℝ≥0∞}
    (hlower : ENNReal.ofReal (C⁻¹ * a) ≤ ENNReal.ofReal (4 / 3 : ℝ) * d)
    (hupper : d ≤ ENNReal.ofReal ((4 / 3 : ℝ) * C * b)) :
    ENNReal.ofReal ((2 * C)⁻¹ * a) < d ∧ d < ENNReal.ofReal ((2 * C) * b) := by
  constructor
  · apply (ENNReal.mul_lt_mul_iff_right
      (by norm_num : ENNReal.ofReal (4 / 3 : ℝ) ≠ 0) ENNReal.ofReal_ne_top).mp
    apply lt_of_lt_of_le _ hlower
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4 / 3)]
    apply (ENNReal.ofReal_lt_ofReal_iff (mul_pos (inv_pos.mpr hC) ha)).mpr
    have hi : (2 * C)⁻¹ = C⁻¹ / 2 := by field_simp
    rw [hi]
    nlinarith [mul_pos (inv_pos.mpr hC) ha]
  · apply hupper.trans_lt
    apply (ENNReal.ofReal_lt_ofReal_iff (mul_pos (mul_pos (by norm_num) hC) hb)).mpr
    nlinarith [mul_pos hC hb]

theorem terminal_intrinsicDiameter_bounds_of_frequently_cComponent
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    (x : H.regularRegion P04)
    (hfreq : ∃ᶠ t in 𝓝[<] T, ∃ ht : t ∈ Ico H.reference.tMinus T,
      ∃ N : SingularCComponent (F.metric t) (F.connection t) H.constant,
        H.reference.forward t ht x ∈ N.carrier)
    (hpos : 0 < (H.terminalConnection P04).scalarCurvature x) :
    ENNReal.ofReal ((2 * H.constant)⁻¹ * sSup (range
      (fun z : connectedComponent x =>
        (H.terminalConnection P04).scalarCurvature z ^ (-1 / 2 : ℝ)))) <
      intrinsicDiameter (H.terminalMetric P04) (connectedComponent x) ∧
    intrinsicDiameter (H.terminalMetric P04) (connectedComponent x) <
      ENNReal.ofReal ((2 * H.constant) * sInf (range
        (fun z : connectedComponent x =>
          (H.terminalConnection P04).scalarCurvature z ^ (-1 / 2 : ℝ)))) := by
  have hA := (H.terminal_topology_of_frequently_cComponent P04 x hfreq).1
  have hne : (connectedComponent x).Nonempty := ⟨x, mem_connectedComponent⟩
  have hposA : ∀ y ∈ connectedComponent x,
      0 < (H.terminalConnection P04).scalarCurvature y := by
    intro y hy
    exact (mul_pos (by norm_num : (0 : ℝ) < 6)
      (mul_pos (inv_pos.mpr H.constant_pos) hpos)).trans_le
      (H.terminal_scalar_lower_bound_of_frequently_cComponent P04 x hfreq hy)
  obtain ⟨hsup_pos, hinf_pos⟩ := H.terminal_scalarRadius_extrema_pos P04 hA hne hposA
  apply strict_doubled_diameter_bounds H.constant_pos hsup_pos hinf_pos
  · apply le_of_tendsto_of_frequently (ENNReal.tendsto_ofReal
      ((H.tendsto_terminal_scalarRadius_sup P04 hA hne hposA).const_mul H.constant⁻¹))
    apply ((H.frequently_cComponent_intrinsicDiameter_bounds P04 x hfreq).and_eventually
      (H.eventually_terminal_intrinsicDiameter_comparison P04 hA
        (by norm_num : (1 : ℝ) < 4 / 3))).mono
    rintro t ⟨hold, hcomp⟩
    exact hold.1.le.trans (hcomp (connectedComponent x) subset_rfl).2
  · apply ge_of_tendsto_of_frequently (ENNReal.tendsto_ofReal
      ((H.tendsto_terminal_scalarRadius_inf P04 hA hne hposA).const_mul
        ((4 / 3 : ℝ) * H.constant)))
    apply ((H.frequently_cComponent_intrinsicDiameter_bounds P04 x hfreq).and_eventually
      (H.eventually_terminal_intrinsicDiameter_comparison P04 hA
        (by norm_num : (1 : ℝ) < 4 / 3))).mono
    rintro t ⟨hold, hcomp⟩
    calc
      intrinsicDiameter (H.terminalMetric P04) (connectedComponent x) ≤
          ENNReal.ofReal (4 / 3 : ℝ) *
            intrinsicDiameter ((H.terminalFlow P04).metric t) (connectedComponent x) :=
        (hcomp (connectedComponent x) subset_rfl).1
      _ ≤ ENNReal.ofReal (4 / 3 : ℝ) * ENNReal.ofReal (H.constant * sInf (range
          (fun z : connectedComponent x => H.reference.scalar t z ^ (-1 / 2 : ℝ)))) :=
        mul_le_mul_right hold.2.le _
      _ = ENNReal.ofReal (((4 / 3 : ℝ) * H.constant) * sInf (range
          (fun z : connectedComponent x => H.reference.scalar t z ^ (-1 / 2 : ℝ)))) := by
        rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4 / 3), mul_assoc]

end PoincareConjecture.SingularTimeAssumptions
