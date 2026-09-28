import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.Calibration
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Component.Reference
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Component.RestrictedDistance
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Component.Distance
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Bounds



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.SingularRegularLimit

theorem inverse_half_power_comparison {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : b ≤ c ^ 2 * a) :
    a ^ (-1 / 2 : ℝ) ≤ c * b ^ (-1 / 2 : ℝ) := by
  have hpow := Real.rpow_le_rpow_of_nonpos hb hab (by norm_num : (-1 / 2 : ℝ) ≤ 0)
  rw [Real.mul_rpow (sq_nonneg c) ha.le] at hpow
  have hcPow : (c ^ 2) ^ (-1 / 2 : ℝ) = c⁻¹ := by
    rw [← Real.rpow_natCast_mul hc.le]
    norm_num [Real.rpow_neg_one]
  rw [hcPow] at hpow
  have h := mul_le_mul_of_nonneg_left hpow hc.le
  simpa only [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul] using h

end PoincareConjecture.SingularRegularLimit

namespace PoincareConjecture.SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}



theorem terminalFlow_reference_intrinsicDiameter
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    (t : ℝ) (ht : t ∈ Ico H.reference.tMinus T) (K : Set (F.slice t).carrier)
    (hregular : H.reference.inverse t ht '' K ⊆ H.reference.regularLimitSet) :
    intrinsicDiameter ((H.terminalFlow P04).metric t)
      (H.regularReferencePreimage P04 t ht K) = intrinsicDiameter (F.metric t) K := by
  let S := H.reference.forward t ht ⁻¹' K
  have hS : S ⊆ H.regularRegion P04 := by
    intro x hx
    exact hregular ⟨H.reference.forward t ht x, hx, H.reference.left_inverse t ht x⟩
  have hdiam := SingularRegularLimit.intrinsicDiameter_restrictToOpen
    (H.regularRegion P04) (H.reference.flow.metric t) ((H.terminalFlow P04).metric t)
    (fun y v w => by
      rw [Poincare.Geometry.Manifold.RegularLevel.mfderiv_opens_subtypeVal]
      exact (H.terminalMetricFamily_inner_of_ne P04 ht.2.ne y v w).symm) S hS
  change intrinsicDiameter ((H.terminalFlow P04).metric t)
    (H.regularReferencePreimage P04 t ht K) =
      intrinsicDiameter (H.reference.flow.metric t) S at hdiam
  rw [hdiam]
  exact (Homothety.metricHomothetyCalculus _ _ _ 1 (by norm_num)
    (H.reference.slice_metric_homothety t ht)).m48_intrinsicDiameter_eq K



theorem eventually_captured_cap_terminal_intrinsicDiameter_bound
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    {A : Set (H.regularRegion P04)} (hA : IsCompact A)
    (x₀ : H.regularRegion P04)
    (hx₀ : 0 < (H.terminalConnection P04).scalarCurvature x₀) :
    ∀ᶠ t in 𝓝[<] T, ∀ ht : t ∈ Ico H.reference.tMinus T,
      ∀ N : CapCertificate (F.metric t), N.cap_constant ≤ H.constant →
      N.connection = F.connection t →
      H.reference.inverse t ht '' N.carrier ⊆ Subtype.val '' A →
      H.reference.forward t ht x₀ ∈ N.core →
      let S := H.regularReferencePreimage P04 t ht N.carrier
      intrinsicDiameter (H.terminalMetric P04) S <
        ENNReal.ofReal (2 * H.constant *
          scalarCurvatureSupOn (H.terminalMetric P04) (H.terminalConnection P04) S ^
            (-1 / 2 : ℝ)) := by
  let Q := (H.terminalConnection P04).scalarCurvature x₀
  let c : ℝ := 11 / 10
  have hc : 1 < c := by norm_num [c]
  have hcpos := zero_lt_one.trans hc
  have hbase : ∀ᶠ t in 𝓝[<] T, Q / 2 < H.reference.scalar t x₀ :=
    (H.tendsto_terminal_scalarCurvature P04 x₀).eventually (Ioi_mem_nhds (half_lt_self hx₀))
  have hδ : 0 < Q / 20 := by dsimp [Q]; positivity
  filter_upwards [hbase, H.eventually_scalar_suprema_close_on_subsets P04 hA hδ,
    H.eventually_terminal_intrinsicDiameter_comparison P04 hA hc] with t htbase hsup hdiameter
  intro ht N hconstant hconnection hcapture hxcore
  dsimp only
  let S := H.regularReferencePreimage P04 t ht N.carrier
  have hxS : x₀ ∈ S := N.core_subset_carrier hxcore
  have hSA : S ⊆ A := H.regularReferencePreimage_subset P04 t ht N.carrier hcapture
  have hregular : H.reference.inverse t ht '' N.carrier ⊆ H.reference.regularLimitSet := by
    rintro y hy
    obtain ⟨x, _, rfl⟩ := hcapture hy
    exact x.property
  let old := scalarCurvatureSupOn (F.metric t) N.connection N.carrier
  let new := scalarCurvatureSupOn (H.terminalMetric P04) (H.terminalConnection P04) S
  have holdpos : 0 < old := N.scalar_sup_pos
  have holdbase : Q / 2 < old := by
    have hpoint := N.scalar_le_sup (N.core_subset_carrier hxcore)
    have hscalar : N.connection.scalarCurvature
        (H.reference.forward t ht x₀) = H.reference.scalar t x₀ := by
      rw [hconnection, H.reference.scalar_pullback]
      rfl
    rw [hscalar] at hpoint
    exact htbase.trans_le hpoint
  have hnewpos : 0 < new := by
    apply hx₀.trans_le
    apply le_csSup
    · apply (hA.bddAbove_image
        (H.terminalConnection P04).continuous_scalarCurvature.continuousOn).mono
      rintro _ ⟨x, rfl⟩
      exact ⟨x, hSA x.property, rfl⟩
    · exact ⟨⟨x₀, hxS⟩, rfl⟩
  have herror := hsup S ⟨x₀, hxS⟩ hSA
  rw [H.scalar_sup_regularReferencePreimage P04 t ht N.carrier hregular,
    ← hconnection] at herror
  have hcompare : new ≤ c ^ 2 * old := by
    have hh := (abs_sub_lt_iff.mp herror).2
    change new - old < Q / 20 at hh
    norm_num [c] at ⊢
    linarith
  have hpower := SingularRegularLimit.inverse_half_power_comparison
    holdpos hnewpos hcpos hcompare
  have hnewdiameter := (hdiameter S hSA).1
  rw [H.terminalFlow_reference_intrinsicDiameter P04 t ht N.carrier hregular] at hnewdiameter
  have holddiameter : intrinsicDiameter (F.metric t) N.carrier ≤
      ENNReal.ofReal (H.constant * old ^ (-1 / 2 : ℝ)) :=
    N.intrinsic_diameter_bound.le.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hconstant (Real.rpow_nonneg holdpos.le _)))
  have hreal : c * H.constant * old ^ (-1 / 2 : ℝ) <
      2 * H.constant * new ^ (-1 / 2 : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hpower (mul_pos hcpos H.constant_pos).le
    have hp : 0 < H.constant * new ^ (-1 / 2 : ℝ) :=
      mul_pos H.constant_pos (Real.rpow_pos_of_pos hnewpos _)
    dsimp [c] at hm ⊢
    nlinarith
  calc
    intrinsicDiameter (H.terminalMetric P04) S ≤
        ENNReal.ofReal c * intrinsicDiameter (F.metric t) N.carrier := hnewdiameter
    _ ≤ ENNReal.ofReal c * ENNReal.ofReal (H.constant * old ^ (-1 / 2 : ℝ)) :=
      mul_le_mul_right holddiameter _
    _ = ENNReal.ofReal (c * H.constant * old ^ (-1 / 2 : ℝ)) := by
      rw [← ENNReal.ofReal_mul hcpos.le]
      congr 1
      ring
    _ < ENNReal.ofReal (2 * H.constant * new ^ (-1 / 2 : ℝ)) :=
      (ENNReal.ofReal_lt_ofReal_iff (mul_pos (mul_pos (by norm_num) H.constant_pos)
        (Real.rpow_pos_of_pos hnewpos _))).mpr hreal

end PoincareConjecture.SingularTimeAssumptions
