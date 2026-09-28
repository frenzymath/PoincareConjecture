import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.ScalarEscape
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Neck.Curvature
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Bounds

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

namespace SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}

theorem exists_compact_containing_scalar_sublevel_tail
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u}) (B : ℝ) :
    ∃ A : Set M, IsCompact A ∧ A ⊆ H.reference.regularLimitSet ∧
      ∃ s : ℝ, H.reference.tMinus < s ∧ s < T ∧
        ∀ t ∈ Ico s T, {x | H.reference.scalar t x ≤ B} ⊆ A := by
  let K := max (H.r₀⁻¹ ^ 2) B + 1
  have hrho : 0 < H.r₀⁻¹ ^ 2 := sq_pos_of_pos (inv_pos.mpr H.r₀_pos)
  have hrhoK : H.r₀⁻¹ ^ 2 ≤ K := by
    dsimp [K]
    linarith [le_max_left (H.r₀⁻¹ ^ 2) B]
  have hBK : B < K := by
    dsimp [K]
    linarith [le_max_right (H.r₀⁻¹ ^ 2) B]
  have hK : 0 < K := hrho.trans_le hrhoK
  obtain ⟨A, hA, hAreg, hcapture⟩ := H.exists_compact_containing_liminf_sublevel P04 (2 * K)
  let delta := 1 / (4 * (H.analytic_constant + 1) * K)
  have hdelta : 0 < delta := by dsimp [delta]; positivity [H.analytic_constant_pos]
  obtain ⟨s, hs, hsT⟩ := exists_between
    (max_lt H.reference.tMinus_lt (sub_lt_self T hdelta))
  have hsref : H.reference.tMinus < s := (le_max_left _ _).trans_lt hs
  refine ⟨A, hA, hAreg, s, hsref, hsT, ?_⟩
  intro t ht x hx
  have htre : H.reference.tMinus < t := hsref.trans_le ht.1
  have hshort : T - t < 1 / (4 * (H.analytic_constant + 1) * K) := by
    have := (le_max_right H.reference.tMinus (T - delta)).trans_lt hs
    change T - t < delta
    linarith [ht.1]
  have hbound : ∀ z ∈ Ico t T, H.reference.scalar z x ≤ 2 * K := by
    intro z hz
    exact (SingularRegularLimit.scalar_lt_two_mul_of_short_tail H.analytic_constant_pos.le
      hrho hrhoK ((H.reference_scalar_continuousOn P04 x).mono
        (Ico_subset_Ico_left htre.le)) (hx.trans_lt hBK)
      (fun w hw => H.reference_scalar_derivative_bound x w ⟨htre.trans hw.1, hw.2⟩)
      hshort z hz).le
  apply hcapture x
  intro a ha
  obtain ⟨z, hz, hzT⟩ := exists_between (max_lt ha ht.2)
  have htz : t < z := (le_max_right a t).trans_lt hz
  exact ⟨z, (le_max_left a t).trans_lt hz, ⟨htre.le.trans htz.le, hzT⟩,
    hbound z ⟨htz.le, hzT⟩⟩

end SingularTimeAssumptions

namespace SingularRegularLimit

theorem exists_neck_cap_compact_capture_threshold :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M]
        {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
        (H : SingularTimeAssumptions F T M) (_P04 : RicciFlowCurvatureTheory.{u}),
        H.epsilon ≤ epsilon₀ → ∀ x ∈ H.reference.regularLimitSet,
          ∃ A : Set M, IsCompact A ∧ A ⊆ H.reference.regularLimitSet ∧
            ∃ s : ℝ, H.reference.tMinus < s ∧ s < T ∧
              ∀ t (ht : t ∈ Ico H.reference.tMinus T), s ≤ t →
                (∀ N : GeneralizedStrongNeck F t H.epsilon,
                  N.center = H.reference.forward t ht x →
                  closure (H.reference.inverse t ht '' N.carrier) ⊆ A) ∧
                (∀ N : CapCertificate (F.metric t), N.cap_constant ≤ H.constant →
                  N.connection = F.connection t →
                  H.reference.forward t ht x ∈ N.core →
                  closure (H.reference.inverse t ht '' N.carrier) ⊆ A) := by
  obtain ⟨epsilon₀, hpos, hsmall, hneck⟩ := GeneralizedStrongNeck.exists_scalar_control.{u}
  refine ⟨epsilon₀, hpos, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ _ F T H P04 hepsilon x hx
  obtain ⟨a, B, U, ha, haT, hB, _, hxU, _, hbound⟩ :=
    H.exists_open_uniform_scalar_tail P04 hx
  obtain ⟨A, hA, hAreg, b, hb, hbT, hcapture⟩ :=
    H.exists_compact_containing_scalar_sublevel_tail P04 (max 2 H.constant * B)
  refine ⟨A, hA, hAreg, max a b, ha.trans_le (le_max_left _ _), max_lt haT hbT, ?_⟩
  intro t ht hst
  have hat : a ≤ t := (le_max_left a b).trans hst
  have hbt : b ≤ t := (le_max_right a b).trans hst
  have hcenter : (F.connection t).scalarCurvature (H.reference.forward t ht x) ≤ B := by
    rw [H.reference.scalar_pullback t ht x]
    exact hbound t ⟨hat, ht.2⟩ x hxU
  have hscalar (y : (F.slice t).carrier) :
      H.reference.scalar t (H.reference.inverse t ht y) =
        (F.connection t).scalarCurvature y := by
    dsimp only [SingularTimeReference.scalar]
    rw [← H.reference.scalar_pullback t ht (H.reference.inverse t ht y),
      H.reference.right_inverse t ht y]
  constructor
  · intro N hc
    apply closure_minimal _ hA.isClosed
    rintro y ⟨z, hz, rfl⟩
    apply hcapture t ⟨hbt, ht.2⟩
    change H.reference.scalar t (H.reference.inverse t ht z) ≤ max 2 H.constant * B
    rw [hscalar]
    have hn := (hneck N hepsilon z hz).2
    rw [hc] at hn
    exact hn.le.trans ((mul_le_mul_of_nonneg_left hcenter (by norm_num)).trans
      (mul_le_mul_of_nonneg_right (le_max_left 2 H.constant) hB.le))
  · intro N hconstant hconnection hxcore
    apply closure_minimal _ hA.isClosed
    rintro y ⟨z, hz, rfl⟩
    apply hcapture t ⟨hbt, ht.2⟩
    change H.reference.scalar t (H.reference.inverse t ht z) ≤ max 2 H.constant * B
    rw [hscalar]
    have hxcarrier := N.core_subset_carrier hxcore
    have hn := N.scalar_lt_constant_mul hxcarrier hz
    have hRpos := N.scalar_pos _ hxcarrier
    rw [hconnection] at hn hRpos
    exact hn.le.trans ((mul_le_mul_of_nonneg_right hconstant hRpos.le).trans
      ((mul_le_mul_of_nonneg_left hcenter H.constant_pos.le).trans
        (mul_le_mul_of_nonneg_right (le_max_right 2 H.constant) hB.le)))

end SingularRegularLimit

end PoincareConjecture
