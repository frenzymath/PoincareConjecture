import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.Calibration
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Bounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}

theorem eventually_captured_cap_terminal_scalar_ratio
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
      (∀ x ∈ S, 0 < (H.terminalConnection P04).scalarCurvature x) ∧
      ∃ b : ℝ, b < 2 * H.constant ∧ ∀ x ∈ S, ∀ y ∈ S,
        (H.terminalConnection P04).scalarCurvature y ≤
          b * (H.terminalConnection P04).scalarCurvature x := by
  let m := (H.terminalConnection P04).scalarCurvature x₀ / 2
  have hm : 0 < m := half_pos hx₀
  let δ := m / (8 * (H.constant + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity [H.constant_pos]
  have hδeq : (H.constant + 1) * δ = m / 8 := by
    dsimp [δ]
    field_simp [ne_of_gt (add_pos H.constant_pos zero_lt_one)]
  have hbase : ∀ᶠ t in 𝓝[<] T, m < H.reference.scalar t x₀ :=
    (H.tendsto_terminal_scalarCurvature P04 x₀).eventually (Ioi_mem_nhds (half_lt_self hx₀))
  have hclose := Metric.tendstoUniformlyOn_iff.mp
    (H.tendstoUniformlyOn_terminal_scalarCurvature P04 hA) δ hδ
  filter_upwards [hbase, hclose] with t hbase hclose
  intro ht N hconstant hconnection hcapture hx₀core
  dsimp only
  let S := H.regularReferencePreimage P04 t ht N.carrier
  have hSA : S ⊆ A := H.regularReferencePreimage_subset P04 t ht N.carrier hcapture
  have hold (x : H.regularRegion P04) :
      N.connection.scalarCurvature (H.reference.forward t ht x) = H.reference.scalar t x := by
    rw [hconnection, H.reference.scalar_pullback]
    rfl
  have herror (x : H.regularRegion P04) (hx : x ∈ S) :
      |H.reference.scalar t x - (H.terminalConnection P04).scalarCurvature x| < δ := by
    simpa only [Real.dist_eq, abs_sub_comm] using hclose x (hSA hx)
  have hlower (x : H.regularRegion P04) (hx : x ∈ S) :
      m ≤ H.constant * H.reference.scalar t x := by
    have hp := N.scalar_pos _ hx
    have hh := N.scalar_lt_constant_mul hx (N.core_subset_carrier hx₀core)
    rw [hold, hold] at hh
    rw [hold] at hp
    exact hbase.le.trans (hh.le.trans (mul_le_mul_of_nonneg_right hconstant hp.le))
  have hnewlower (x : H.regularRegion P04) (hx : x ∈ S) :
      7 * m / 8 ≤ H.constant * (H.terminalConnection P04).scalarCurvature x := by
    have hh := (abs_sub_lt_iff.mp (herror x hx)).1
    have hmul := mul_lt_mul_of_pos_left hh H.constant_pos
    have hlo := hlower x hx
    nlinarith
  constructor
  · intro x hx
    have hh : 0 < H.constant * (H.terminalConnection P04).scalarCurvature x :=
      (by positivity : 0 < 7 * m / 8).trans_le (hnewlower x hx)
    exact pos_of_mul_pos_right hh H.constant_pos.le
  · refine ⟨3 * H.constant / 2, by nlinarith [H.constant_pos], ?_⟩
    intro x hx y hy
    have hxpos := N.scalar_pos _ hx
    have hratio := N.scalar_lt_constant_mul hx hy
    rw [hold, hold] at hratio
    rw [hold] at hxpos
    have hratio' := hratio.le.trans (mul_le_mul_of_nonneg_right hconstant hxpos.le)
    have hex := (abs_sub_lt_iff.mp (herror x hx)).1
    have hey := (abs_sub_lt_iff.mp (herror y hy)).2
    have hmul := mul_lt_mul_of_pos_left hex H.constant_pos
    have hlo := hnewlower x hx
    nlinarith

end PoincareConjecture.SingularTimeAssumptions
