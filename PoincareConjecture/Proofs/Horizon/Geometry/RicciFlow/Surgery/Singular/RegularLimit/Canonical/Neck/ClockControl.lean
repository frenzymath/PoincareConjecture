import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.LateControl
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Neck.BackwardClock



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




theorem exists_late_neck_clock_control
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    (x : H.regularRegion P04)
    (hQ : 0 < (H.terminalConnection P04).scalarCurvature x) :
    ∃ a : ℝ, H.reference.tMinus < a ∧ a < T ∧
      ∀ t (ht : t ∈ Ico H.reference.tMinus T), a < t →
        ∀ N : GeneralizedStrongNeck F t H.epsilon,
          N.center = H.reference.forward t ht x →
          (F.connection t).scalarCurvature N.center <
            (H.terminalConnection P04).scalarCurvature x →
          let c := (H.terminalConnection P04).scalarCurvature x /
            (F.connection t).scalarCurvature N.center
          let d := (H.terminalConnection P04).scalarCurvature x * (T - t)
          1 ≤ c ∧ c ≤ 6 / 5 ∧ c - 1 ≤ H.epsilon / 4 ∧
            0 ≤ d ∧ d ≤ H.epsilon / 4 := by
  let Q := (H.terminalConnection P04).scalarCurvature x
  have hscalar := H.tendsto_terminal_scalarCurvature P04 x
  have hratio : Tendsto (fun t => Q / H.reference.scalar t x) (𝓝[<] T) (𝓝 1) := by
    simpa only [Q, Pi.div_def, div_self hQ.ne'] using
      (tendsto_const_nhds (x := Q)).div hscalar hQ.ne'
  have htime : Tendsto (fun t : ℝ => Q * (T - t)) (𝓝[<] T) (𝓝 0) := by
    have hid : Tendsto (fun t : ℝ => t) (𝓝[<] T) (𝓝 T) :=
      continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
    simpa using (tendsto_const_nhds (x := Q)).mul
      ((tendsto_const_nhds (x := T)).sub hid)
  have hsmall : ∀ᶠ t in 𝓝[<] T,
      Q / H.reference.scalar t x < 6 / 5 ∧
        Q / H.reference.scalar t x - 1 < H.epsilon / 4 ∧
        Q * (T - t) < H.epsilon / 4 := by
    have hε := H.epsilon_pos
    have hepsilon : 0 < H.epsilon / 4 := by positivity
    have hratio' : Tendsto (fun t => Q / H.reference.scalar t x - 1)
        (𝓝[<] T) (𝓝 0) := by simpa using hratio.sub_const 1
    filter_upwards [hratio.eventually_lt_const (by norm_num : (1 : ℝ) < 6 / 5),
      hratio'.eventually_lt_const hepsilon, htime.eventually_lt_const hepsilon]
      with t h₁ h₂ h₃
    exact ⟨h₁, h₂, h₃⟩
  obtain ⟨s, hsT, hs⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hsmall
  obtain ⟨b, hb, hbT⟩ := exists_between H.reference.tMinus_lt
  refine ⟨max s b, hb.trans_le (le_max_right _ _), max_lt hsT hbT, ?_⟩
  intro t ht hat N hcenter hbelow
  obtain ⟨h₁, h₂, h₃⟩ := hs ⟨(le_max_left s b).trans_lt hat, ht.2⟩
  have heq : (F.connection t).scalarCurvature N.center = H.reference.scalar t x := by
    rw [hcenter, H.reference.scalar_pullback]
    rfl
  refine ⟨?_, ?_, ?_, ?_, h₃.le⟩
  · apply (le_div_iff₀ N.scalar_center_pos).2
    simpa only [one_mul] using hbelow.le
  · simpa only [heq] using h₁.le
  · simpa only [heq] using h₂.le
  · exact mul_nonneg hQ.le (sub_nonneg.mpr ht.2.le)

end PoincareConjecture.SingularTimeAssumptions
