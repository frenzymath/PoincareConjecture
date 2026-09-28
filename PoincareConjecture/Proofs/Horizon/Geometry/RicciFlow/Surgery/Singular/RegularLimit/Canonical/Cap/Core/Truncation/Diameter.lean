import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.Core.Truncation.Model
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Metric.IntrinsicDiameter
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.Diameter

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.CapCertificate

theorem exists_truncated_intrinsicDiameter_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
      ∀ C : CapCertificate g, C.epsilon ≤ ε₀ →
      ∀ b ∈ Ioo (-C.epsilon⁻¹) C.epsilon⁻¹,
        intrinsicDiameter g (C.closed_core ∪ C.end_neck.region (-C.epsilon⁻¹) b) ≤
          ENNReal.ofReal (11 / 10 : ℝ) * intrinsicDiameter g C.carrier := by
  obtain ⟨ε₀, hε₀, hsmall, htransport⟩ := exists_metric_truncation_threshold.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g C hε b hb
  obtain ⟨E, hsource, htarget, hE, _, _, hbound⟩ := htransport C hε b hb
  have hdiam := g.intrinsicDiameter_image_le_of_tangentNorm_le g E.open_source
    (hE.of_le (by simp)) (by norm_num : (0 : ℝ) < 11 / 10) hbound
  rw [E.image_source_eq_target, htarget, hsource] at hdiam
  exact hdiam

end PoincareConjecture.CapCertificate

namespace PoincareConjecture.SingularRegularLimit

theorem exists_truncated_cap_terminal_intrinsicDiameter_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M]
        {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
        (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
        {A : Set (H.regularRegion P04)}, IsCompact A →
        ∀ x₀ : H.regularRegion P04, 0 < (H.terminalConnection P04).scalarCurvature x₀ →
      ∀ᶠ t in 𝓝[<] T, ∀ ht : t ∈ Ico H.reference.tMinus T,
        ∀ N : CapCertificate (F.metric t), N.epsilon ≤ ε₀ →
        N.cap_constant ≤ H.constant → N.connection = F.connection t →
        H.reference.inverse t ht '' N.carrier ⊆ Subtype.val '' A →
        H.reference.forward t ht x₀ ∈ N.core →
        ∀ b ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹,
        let S := H.regularReferencePreimage P04 t ht
          (N.closed_core ∪ N.end_neck.region (-N.epsilon⁻¹) b)
        intrinsicDiameter (H.terminalMetric P04) S <
          ENNReal.ofReal (2 * H.constant *
            scalarCurvatureSupOn (H.terminalMetric P04) (H.terminalConnection P04) S ^
              (-1 / 2 : ℝ)) := by
  obtain ⟨ε₀, hε₀, hsmall, htrunc⟩ :=
    CapCertificate.exists_truncated_intrinsicDiameter_threshold.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ _ F T H P04 A hA x₀ hx₀
  let Q := (H.terminalConnection P04).scalarCurvature x₀
  let c : ℝ := 11 / 10
  have hc : 1 < c := by norm_num [c]
  have hcpos := zero_lt_one.trans hc
  have hbase : ∀ᶠ t in 𝓝[<] T, Q / 2 < H.reference.scalar t x₀ :=
    (H.tendsto_terminal_scalarCurvature P04 x₀).eventually (Ioi_mem_nhds (half_lt_self hx₀))
  have hδ : 0 < Q / 20 := by dsimp [Q]; positivity
  filter_upwards [hbase, H.eventually_scalar_suprema_close_on_subsets P04 hA hδ,
    H.eventually_terminal_intrinsicDiameter_comparison P04 hA hc] with t htbase hsup hdiameter
  intro ht N hε hconstant hconnection hcapture hxcore b hb
  dsimp only
  let U := N.closed_core ∪ N.end_neck.region (-N.epsilon⁻¹) b
  let S := H.regularReferencePreimage P04 t ht U
  let S₀ := H.regularReferencePreimage P04 t ht N.carrier
  have hUsub : U ⊆ N.carrier :=
    union_subset N.closed_core_subset_carrier (fun _ hx => N.end_neck_subset hx.1)
  have hxS : x₀ ∈ S := Or.inl (N.core_subset_closed_core hxcore)
  have hxS₀ : x₀ ∈ S₀ := N.core_subset_carrier hxcore
  have hSS₀ : S ⊆ S₀ := preimage_mono hUsub
  have hS₀A : S₀ ⊆ A := H.regularReferencePreimage_subset P04 t ht N.carrier hcapture
  have hSA : S ⊆ A := hSS₀.trans hS₀A
  have hregular : H.reference.inverse t ht '' N.carrier ⊆ H.reference.regularLimitSet := by
    rintro y hy
    obtain ⟨x, _, rfl⟩ := hcapture hy
    exact x.property
  have hUregular : H.reference.inverse t ht '' U ⊆ H.reference.regularLimitSet :=
    (image_mono hUsub).trans hregular
  let old := scalarCurvatureSupOn (F.metric t) N.connection N.carrier
  let new := scalarCurvatureSupOn (H.terminalMetric P04) (H.terminalConnection P04) S
  let full := scalarCurvatureSupOn (H.terminalMetric P04) (H.terminalConnection P04) S₀
  have holdpos : 0 < old := N.scalar_sup_pos
  have holdbase : Q / 2 < old := by
    have hpoint := N.scalar_le_sup (N.core_subset_carrier hxcore)
    have hscalar : N.connection.scalarCurvature
        (H.reference.forward t ht x₀) = H.reference.scalar t x₀ := by
      rw [hconnection, H.reference.scalar_pullback]
      rfl
    rw [hscalar] at hpoint
    exact htbase.trans_le hpoint
  have hbdd (V : Set (H.regularRegion P04)) (hVA : V ⊆ A) :
      BddAbove (range (fun x : V => (H.terminalConnection P04).scalarCurvature x)) := by
    apply (hA.bddAbove_image
      (H.terminalConnection P04).continuous_scalarCurvature.continuousOn).mono
    rintro _ ⟨x, rfl⟩
    exact ⟨x, hVA x.property, rfl⟩
  have hnewpos : 0 < new :=
    hx₀.trans_le (le_csSup (hbdd S hSA) ⟨⟨x₀, hxS⟩, rfl⟩)
  have hnewfull : new ≤ full := by
    apply csSup_le
    · exact ⟨_, ⟨⟨x₀, hxS⟩, rfl⟩⟩
    · rintro _ ⟨x, rfl⟩
      exact le_csSup (hbdd S₀ hS₀A) ⟨⟨x, hSS₀ x.property⟩, rfl⟩
  have herror := hsup S₀ ⟨x₀, hxS₀⟩ hS₀A
  rw [H.scalar_sup_regularReferencePreimage P04 t ht N.carrier hregular,
    ← hconnection] at herror
  have hcompare : new ≤ c ^ 2 * old := by
    have hh := (abs_sub_lt_iff.mp herror).2
    change full - old < Q / 20 at hh
    norm_num [c] at ⊢
    linarith
  have hpower := SingularRegularLimit.inverse_half_power_comparison
    holdpos hnewpos hcpos hcompare
  have hnewdiameter := (hdiameter S hSA).1
  rw [H.terminalFlow_reference_intrinsicDiameter P04 t ht U hUregular] at hnewdiameter
  have holddiameter : intrinsicDiameter (F.metric t) N.carrier ≤
      ENNReal.ofReal (H.constant * old ^ (-1 / 2 : ℝ)) :=
    N.intrinsic_diameter_bound.le.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hconstant (Real.rpow_nonneg holdpos.le _)))
  have hreal : c * c * H.constant * old ^ (-1 / 2 : ℝ) <
      2 * H.constant * new ^ (-1 / 2 : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hpower
      (mul_pos (mul_pos hcpos hcpos) H.constant_pos).le
    have hp : 0 < H.constant * new ^ (-1 / 2 : ℝ) :=
      mul_pos H.constant_pos (Real.rpow_pos_of_pos hnewpos _)
    dsimp [c] at hm ⊢
    nlinarith
  calc
    intrinsicDiameter (H.terminalMetric P04) S ≤
        ENNReal.ofReal c * intrinsicDiameter (F.metric t) U := hnewdiameter
    _ ≤ ENNReal.ofReal c * (ENNReal.ofReal c * intrinsicDiameter (F.metric t) N.carrier) :=
      mul_le_mul_right (htrunc N hε b hb) _
    _ ≤ ENNReal.ofReal c * (ENNReal.ofReal c *
        ENNReal.ofReal (H.constant * old ^ (-1 / 2 : ℝ))) :=
      mul_le_mul_right (mul_le_mul_right holddiameter _) _
    _ = ENNReal.ofReal (c * c * H.constant * old ^ (-1 / 2 : ℝ)) := by
      rw [← ENNReal.ofReal_mul hcpos.le, ← ENNReal.ofReal_mul hcpos.le]
      congr 1
      ring
    _ < ENNReal.ofReal (2 * H.constant * new ^ (-1 / 2 : ℝ)) :=
      (ENNReal.ofReal_lt_ofReal_iff (mul_pos (mul_pos (by norm_num) H.constant_pos)
        (Real.rpow_pos_of_pos hnewpos _))).mpr hreal

end PoincareConjecture.SingularRegularLimit
