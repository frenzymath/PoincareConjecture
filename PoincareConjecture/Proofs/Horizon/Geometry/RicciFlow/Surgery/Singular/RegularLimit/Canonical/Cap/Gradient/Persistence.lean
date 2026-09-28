import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.Gradient.Transport
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.ScalarRatio
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.RicciFlow



theorem tendstoUniformlyOn_scalarCurvature_rpow_of_nonneg
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {J : Set ℝ} (G : RicciFlow n M J)
    {T : ℝ} (hT : T ∈ J) {A : Set M} (hA : IsCompact A)
    {p : ℝ} (hp : 0 ≤ p) :
    TendstoUniformlyOn (fun t x => ((G.connection t).scalarCurvature x) ^ p)
      (fun x => ((G.connection T).scalarCurvature x) ^ p) (𝓝[J] T) A := by
  have hcontinuous : ContinuousOn
      (fun z : ℝ × M => ((G.connection z.1).scalarCurvature z.2) ^ p) (J ×ˢ univ) :=
    G.contMDiffOn_scalarCurvature.continuousOn.rpow_const (fun _ _ => Or.inr hp)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  obtain ⟨V, hV, hbound⟩ := hA.mem_uniformity_of_prod
    (f := fun t x => ((G.connection t).scalarCurvature x) ^ p)
    (hcontinuous.mono (prod_mono subset_rfl (subset_univ A))) hT
    (Metric.dist_mem_uniformity hε)
  filter_upwards [hV] with t ht x hx
  have hb : dist (((G.connection t).scalarCurvature x) ^ p)
      (((G.connection T).scalarCurvature x) ^ p) < ε := hbound t ht x hx
  rwa [dist_comm] at hb

end PoincareConjecture.RicciFlow

namespace PoincareConjecture.SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}



theorem eventually_captured_cap_terminal_scalarGradient_bound
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    {A : Set (H.regularRegion P04)} (hA : IsCompact A)
    (x₀ : H.regularRegion P04)
    (hx₀ : 0 < (H.terminalConnection P04).scalarCurvature x₀) :
    ∀ᶠ t in 𝓝[<] T, ∀ ht : t ∈ Ico H.reference.tMinus T,
      ∀ N : CapCertificate (F.metric t), N.cap_constant ≤ H.constant →
      N.connection = F.connection t →
      H.reference.inverse t ht '' N.carrier ⊆ Subtype.val '' A →
      H.reference.forward t ht x₀ ∈ N.core →
      ∃ b : ℝ, b < 2 * H.constant ∧
        ∀ x ∈ H.regularReferencePreimage P04 t ht N.carrier,
          scalarGradientNorm (H.terminalMetric P04) (H.terminalConnection P04) x ≤
            b * ((H.terminalConnection P04).scalarCurvature x) ^ (3 / 2 : ℝ) := by
  let G := H.terminalFlow P04
  let m := (H.terminalConnection P04).scalarCurvature x₀ / 2
  have hm : 0 < m := half_pos hx₀
  let a := m / (2 * H.constant)
  have ha : 0 < a := by dsimp [a]; positivity [H.constant_pos]
  let δ := H.constant * a ^ (3 / 2 : ℝ) / (4 * (H.constant + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity [H.constant_pos]
  have hδeq : (H.constant + 1) * δ = H.constant * a ^ (3 / 2 : ℝ) / 4 := by
    dsimp [δ]
    field_simp [ne_of_gt (add_pos H.constant_pos zero_lt_one)]
  have hfilter : 𝓝[<] T ≤ 𝓝[Ioc H.reference.tMinus T] T :=
    nhdsWithin_le_of_mem (Ioc_mem_nhdsLT H.reference.tMinus_lt)
  have hscalar : ∀ᶠ t in 𝓝[<] T, m < H.reference.scalar t x₀ :=
    (H.tendsto_terminal_scalarCurvature P04 x₀).eventually (Ioi_mem_nhds (half_lt_self hx₀))
  have hclose := Metric.tendstoUniformlyOn_iff.mp
    (H.tendstoUniformlyOn_terminal_scalarCurvature P04 hA) a ha
  have hgradient := hfilter (Metric.tendstoUniformlyOn_iff.mp
    (G.tendstoUniformlyOn_scalarGradientNorm ⟨H.reference.tMinus_lt, le_rfl⟩ hA) δ hδ)
  have hpower := hfilter (Metric.tendstoUniformlyOn_iff.mp
    (G.tendstoUniformlyOn_scalarCurvature_rpow_of_nonneg
      ⟨H.reference.tMinus_lt, le_rfl⟩ hA (by norm_num : 0 ≤ (3 / 2 : ℝ))) δ hδ)
  filter_upwards [hscalar, hclose, hgradient, hpower] with t hscalar hclose hgradient hpower
  intro ht N hconstant hconnection hcapture hx₀core
  refine ⟨3 * H.constant / 2, by nlinarith [H.constant_pos], ?_⟩
  intro x hx
  have hxA := H.regularReferencePreimage_subset P04 t ht N.carrier hcapture hx
  have hpos := N.scalar_pos _ hx
  have hratio := N.scalar_lt_constant_mul hx (N.core_subset_carrier hx₀core)
  rw [hconnection, H.reference.scalar_pullback, H.reference.scalar_pullback] at hratio
  rw [hconnection, H.reference.scalar_pullback] at hpos
  have hlower : m ≤ H.constant * H.reference.scalar t x :=
    hscalar.le.trans (hratio.le.trans (mul_le_mul_of_nonneg_right hconstant hpos.le))
  have herror := hclose x hxA
  rw [Real.dist_eq] at herror
  have hmul := mul_lt_mul_of_pos_left (abs_sub_lt_iff.mp herror).2 H.constant_pos
  have hacancel : H.constant * a = m / 2 := by
    dsimp [a]
    field_simp [H.constant_pos.ne']
  have hnewlower : a ≤ (H.terminalConnection P04).scalarCurvature x := by
    apply (mul_le_mul_iff_right₀ H.constant_pos).mp
    nlinarith
  have hnewpow := Real.rpow_le_rpow ha.le hnewlower (by norm_num : 0 ≤ (3 / 2 : ℝ))
  have hgrad := hgradient x hxA
  rw [Real.dist_eq, H.terminalFlow_scalarGradientNorm_at_terminal P04,
    H.terminalFlow_scalarGradientNorm_of_lt P04 t ht] at hgrad
  have hpow := hpower x hxA
  rw [Real.dist_eq, H.terminalFlow_scalar_at_terminal P04,
    H.terminalFlow_scalar_of_ne P04 ht.2.ne] at hpow
  obtain ⟨b, hb, hbound⟩ := N.gradient_bound
  have hold := (hbound _ hx).trans (mul_le_mul_of_nonneg_right
    (hb.le.trans hconstant) (Real.rpow_nonneg (N.scalar_pos _ hx).le _))
  rw [hconnection, H.reference.scalar_pullback] at hold
  change scalarGradientNorm (F.metric t) (F.connection t)
      (H.reference.forward t ht x) ≤ H.constant * H.reference.scalar t x ^ (3 / 2 : ℝ) at hold
  have hpowmul := mul_lt_mul_of_pos_left (abs_sub_lt_iff.mp hpow).2 H.constant_pos
  have hmargin := mul_le_mul_of_nonneg_left hnewpow H.constant_pos.le
  have hnonneg := mul_nonneg H.constant_pos.le (Real.rpow_nonneg (ha.le.trans hnewlower) (3 / 2 : ℝ))
  have hgrad' := (abs_sub_lt_iff.mp hgrad).1
  nlinarith only [hold, hgrad', hpowmul, hmargin, hδeq, hnonneg]

end PoincareConjecture.SingularTimeAssumptions
