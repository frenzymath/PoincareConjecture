import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.RegularSet

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}

theorem exists_scalar_sublevel_tail (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) (B : ℝ) :
    ∃ s : ℝ, H.reference.tMinus < s ∧ s < T ∧
      ∀ t ∈ Ico s T, {x | H.reference.scalar t x ≤ B} ⊆ H.reference.regularLimitSet := by
  let K := max (H.r₀⁻¹ ^ 2) B + 1
  have hrho : 0 < H.r₀⁻¹ ^ 2 := sq_pos_of_pos (inv_pos.mpr H.r₀_pos)
  have hrhoK : H.r₀⁻¹ ^ 2 ≤ K := by dsimp [K]; linarith [le_max_left (H.r₀⁻¹ ^ 2) B]
  have hBK : B < K := by dsimp [K]; linarith [le_max_right (H.r₀⁻¹ ^ 2) B]
  have hK : 0 < K := hrho.trans_le hrhoK
  let delta := 1 / (4 * (H.analytic_constant + 1) * K)
  have hdelta : 0 < delta := by dsimp [delta]; positivity [H.analytic_constant_pos]
  obtain ⟨s, hs, hsT⟩ := exists_between
    (max_lt H.reference.tMinus_lt (sub_lt_self T hdelta))
  have hsref := (le_max_left H.reference.tMinus (T - delta)).trans_lt hs
  refine ⟨s, hsref, hsT, ?_⟩
  intro t ht x hx
  have htre : H.reference.tMinus < t := hsref.trans_le ht.1
  have hshort : T - t < 1 / (4 * (H.analytic_constant + 1) * K) := by
    have := (le_max_right H.reference.tMinus (T - delta)).trans_lt hs
    change T - t < delta
    linarith [ht.1]
  apply H.mem_regularLimitSet_of_scalar_tail htre.le ht.2
  intro z hz
  exact (SingularRegularLimit.scalar_lt_two_mul_of_short_tail H.analytic_constant_pos.le
    hrho hrhoK ((H.reference_scalar_continuousOn P04 x).mono
      (Ico_subset_Ico_left htre.le)) (hx.trans_lt hBK)
    (fun w hw => H.reference_scalar_derivative_bound x w ⟨htre.trans hw.1, hw.2⟩)
    hshort z hz).le

theorem scalar_diverges_uniformly_off_regularLimitSet (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) (B : ℝ) :
    ∃ s : ℝ, H.reference.tMinus < s ∧ s < T ∧ ∀ t ∈ Ico s T,
      ∀ x ∉ H.reference.regularLimitSet, B < H.reference.scalar t x := by
  obtain ⟨s, hs, hsT, hsub⟩ := H.exists_scalar_sublevel_tail P04 B
  exact ⟨s, hs, hsT, fun t ht x hx => lt_of_not_ge (fun h => hx (hsub t ht h))⟩

theorem exists_compact_scalar_sublevel_tail (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) (B : ℝ) :
    ∃ s : ℝ, H.reference.tMinus < s ∧ s < T ∧ ∀ t ∈ Ico s T,
      IsCompact {x | H.reference.scalar t x ≤ B} ∧
        {x | H.reference.scalar t x ≤ B} ⊆ H.reference.regularLimitSet := by
  let : CompactSpace M := H.compact_reference
  obtain ⟨s, hs, hsT, hsub⟩ := H.exists_scalar_sublevel_tail P04 B
  refine ⟨s, hs, hsT, fun t ht => ⟨?_, hsub t ht⟩⟩
  exact (isClosed_le
    (H.reference_scalar_continuous P04 t ⟨hs.le.trans ht.1, ht.2⟩) continuous_const).isCompact

theorem exists_compact_containing_liminf_sublevel (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) (B : ℝ) :
    ∃ A : Set M, IsCompact A ∧ A ⊆ H.reference.regularLimitSet ∧
      ∀ x : M, (∀ a : ℝ, a < T → ∃ t : ℝ, a < t ∧
        t ∈ Ico H.reference.tMinus T ∧ H.reference.scalar t x ≤ B) → x ∈ A := by
  let K := max (H.r₀⁻¹ ^ 2) B + 1
  have hrho : 0 < H.r₀⁻¹ ^ 2 := sq_pos_of_pos (inv_pos.mpr H.r₀_pos)
  have hrhoK : H.r₀⁻¹ ^ 2 ≤ K := by dsimp [K]; linarith [le_max_left (H.r₀⁻¹ ^ 2) B]
  have hBK : B < K := by dsimp [K]; linarith [le_max_right (H.r₀⁻¹ ^ 2) B]
  have hK : 0 < K := hrho.trans_le hrhoK
  let delta := 1 / (4 * (H.analytic_constant + 1) * K)
  have hdelta : 0 < delta := by dsimp [delta]; positivity [H.analytic_constant_pos]
  obtain ⟨a, ha, haT, hcompact⟩ := H.exists_compact_scalar_sublevel_tail P04 (2 * K)
  obtain ⟨s, hs, hsT⟩ := exists_between (max_lt haT (sub_lt_self T hdelta))
  have has : a < s := (le_max_left a (T - delta)).trans_lt hs
  have hsref : H.reference.tMinus < s := ha.trans has
  have hshort : T - s < delta := by
    have := (le_max_right a (T - delta)).trans_lt hs
    linarith
  refine ⟨{x | H.reference.scalar s x ≤ 2 * K},
    (hcompact s ⟨has.le, hsT⟩).1, (hcompact s ⟨has.le, hsT⟩).2, ?_⟩
  intro x hx
  obtain ⟨t, hst, ht, hscalar⟩ := hx s hsT
  have hstcont : ContinuousOn (fun z => H.reference.scalar z x) (Icc s t) :=
    (H.reference_scalar_continuousOn P04 x).mono
      (fun z hz => ⟨hsref.le.trans hz.1, hz.2.trans_lt ht.2⟩)
  have h := SingularRegularLimit.scalar_lt_two_mul_of_short_interval_backward
    H.analytic_constant_pos.le hrho hrhoK hstcont (hscalar.trans_lt hBK)
    (fun z hz => H.reference_scalar_derivative_bound x z
      ⟨hsref.trans hz.1, hz.2.trans ht.2⟩)
    ((sub_le_sub_right ht.2.le s).trans_lt hshort) s ⟨le_rfl, hst.le⟩
  exact h.le

end PoincareConjecture.SingularTimeAssumptions
