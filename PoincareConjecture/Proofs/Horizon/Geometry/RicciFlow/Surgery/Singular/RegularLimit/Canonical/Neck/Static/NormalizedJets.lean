import PoincareConjecture.Proofs.Ch01.CurvatureConnection
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Neck.Static.UniformJets
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Metric.UniformScalar



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 800000

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.SingularTimeAssumptions

open MetricSurgery

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}

theorem exists_late_static_neck_normalized_jet_small
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    {A : Set (H.regularRegion P04)} (hA : IsCompact A)
    {ε l u : ℝ} (hε : ε ≤ 1 / 200) (hl : 0 < l) (hu : 0 < u)
    (m : ℕ) (hm : m ≤ ⌊ε⁻¹⌋₊) {η : ℝ} (hη : 0 < η) :
    ∃ s : ℝ, H.reference.tMinus < s ∧ s < T ∧
      ∀ t ∈ Ico s T, ∀ N : EpsilonNeck ((H.terminalFlow P04).metric t),
        N.epsilon = ε → N.carrier ⊆ A →
        l ≤ N.connection.scalarCurvature N.center →
        N.connection.scalarCurvature N.center ≤ u →
        0 < ((H.terminalFlow P04).connection T).scalarCurvature N.center ∧
        ∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
        ∀ j ≤ m,
          ‖iteratedFDeriv ℝ j (fun p =>
            ((H.terminalFlow P04).connection T).scalarCurvature N.center •
                ((H.terminalFlow P04).metric T).pullbackCoefficients
                  (centeredNeckLift N z.1 z.2) p -
              N.connection.scalarCurvature N.center •
                ((H.terminalFlow P04).metric t).pullbackCoefficients
                  (centeredNeckLift N z.1 z.2) p) 0‖ ≤ η := by
  obtain ⟨sJ, B, hsJ, hsJT, hB, hjets⟩ :=
    H.exists_uniform_static_neck_coordinate_tail_bound P04 hA hε hl hu m hm
  obtain ⟨Z, hZ, hinit⟩ := exists_centeredNeck_initial_jet_bound.{u} m
  let Z₀ := Z / l
  have hZ₀ : 0 ≤ Z₀ := (div_pos hZ hl).le
  let δ := min 1 (min (l / 2) (η / (2 * (Z₀ + 1))))
  have hδ : 0 < δ := lt_min zero_lt_one (lt_min (by positivity) (by positivity))
  have hδone : δ ≤ 1 := min_le_left _ _
  have hδl : δ ≤ l / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδη : δ ≤ η / (2 * (Z₀ + 1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hscalar := Metric.tendstoUniformlyOn_iff.mp
    (H.tendstoUniformlyOn_terminal_scalarCurvature P04 hA) δ hδ
  obtain ⟨sR, hsRT, hscalar⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hscalar
  let a := η / (2 * ((u + 1) * B + 1))
  have ha : 0 < a := by dsimp [a]; positivity
  obtain ⟨s, hs, hsT⟩ := exists_between (max_lt hsJT (max_lt hsRT (sub_lt_self T ha)))
  have hssJ : sJ < s := (le_max_left _ _).trans_lt hs
  have hssR : sR < s := (le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hs)
  have hssmall : T - a < s := (le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hs)
  refine ⟨s, hsJ.trans hssJ, hsT, ?_⟩
  intro t ht N hNε hNA hql hqu
  let q := N.connection.scalarCurvature N.center
  let Q := ((H.terminalFlow P04).connection T).scalarCurvature N.center
  have hq : 0 < q := N.scalar_center_pos
  have hcenterA := hNA (N.central_sphere_subset N.center_on_central_sphere)
  have hqeq : q = H.reference.scalar t N.center :=
    (N.connection.scalarCurvature_eq ((H.terminalFlow P04).connection t) N.center).trans
      (H.terminalFlow_scalar_of_ne P04 ht.2.ne N.center)
  have hgap : |Q - q| < δ := by
    have hh := hscalar ⟨hssR.trans_le ht.1, ht.2⟩ N.center hcenterA
    simpa only [Real.dist_eq, ← H.terminalFlow_scalar_at_terminal P04 N.center, ← hqeq] using hh
  have hQ : 0 < Q := by
    have hh := (abs_lt.mp hgap).1
    change l ≤ q at hql
    linarith
  have hQu : Q ≤ u + 1 := by
    have hh := (abs_lt.mp hgap).2
    change q ≤ u at hqu
    linarith
  refine ⟨hQ, ?_⟩
  intro z hz j hj
  let f := centeredNeckLift N z.1 z.2
  let gT := ((H.terminalFlow P04).metric T).pullbackCoefficients f
  let gt := ((H.terminalFlow P04).metric t).pullbackCoefficients f
  have hf := centeredNeckLift_contMDiffAt N z.1 z.2 (zero_mem_centeredNeckDomain N hz)
  have hgT : ContDiffAt ℝ ∞ gT 0 := ((H.terminalFlow P04).metric T).contDiffAt_pullbackCoefficients hf
  have hgt : ContDiffAt ℝ ∞ gt 0 := ((H.terminalFlow P04).metric t).contDiffAt_pullbackCoefficients hf
  have hi : ‖iteratedFDeriv ℝ j gt 0‖ ≤ Z₀ := by
    have hh := hinit N (by rw [hNε]; linarith) (hNε ▸ hm) z hz j hj
    rw [normalizedNeckMetric_centered_jet N z hz, norm_smul,
      Real.norm_eq_abs, abs_of_pos N.scalar_center_pos] at hh
    apply (le_div_iff₀ hl).mpr
    have hscale := mul_le_mul_of_nonneg_right hql (norm_nonneg (iteratedFDeriv ℝ j gt 0))
    nlinarith
  have htime := hjets t ⟨hssJ.le.trans ht.1, ht.2⟩ N hNε hNA hql hqu
    z hz T ⟨ht.2.le, le_rfl⟩ j hj
  have heq : iteratedFDeriv ℝ j (fun p => Q • gT p - q • gt p) 0 =
      Q • (iteratedFDeriv ℝ j gT 0 - iteratedFDeriv ℝ j gt 0) +
        (Q - q) • iteratedFDeriv ℝ j gt 0 := by
    rw [fun_iteratedFDeriv_sub_apply
      ((hgT.const_smul Q).of_le (by exact_mod_cast le_top))
      ((hgt.const_smul q).of_le (by exact_mod_cast le_top)),
      iteratedFDeriv_const_smul_apply' (hgT.of_le (by exact_mod_cast le_top)),
      iteratedFDeriv_const_smul_apply' (hgt.of_le (by exact_mod_cast le_top))]
    module
  rw [heq]
  have hn := norm_add_le (Q • (iteratedFDeriv ℝ j gT 0 - iteratedFDeriv ℝ j gt 0))
    ((Q - q) • iteratedFDeriv ℝ j gt 0)
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hQ] at hn
  have htbound := mul_le_mul hQu htime (norm_nonneg _) (by positivity : 0 ≤ u + 1)
  have hqbound := mul_le_mul hgap.le hi (norm_nonneg _) hδ.le
  have hδbound := (le_div_iff₀ (by positivity : 0 < 2 * (Z₀ + 1))).1 hδη
  have hdt : 0 ≤ T - t := sub_nonneg.mpr ht.2.le
  have hnear : T - t < a := by linarith [ht.1]
  have htb := (lt_div_iff₀ (by positivity : 0 < 2 * ((u + 1) * B + 1))).1 hnear
  nlinarith

end PoincareConjecture.SingularTimeAssumptions
