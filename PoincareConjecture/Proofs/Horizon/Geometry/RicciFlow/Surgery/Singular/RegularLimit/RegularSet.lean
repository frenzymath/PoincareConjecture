import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Reference
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.ScalarComparison











set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}


theorem mem_regularLimitSet_of_scalar_tail (H : SingularTimeAssumptions F T M)
    {x : M} {s B : ℝ} (hs : H.reference.tMinus ≤ s) (hsT : s < T)
    (hbound : ∀ t ∈ Ico s T, H.reference.scalar t x ≤ B) :
    x ∈ H.reference.regularLimitSet := by
  refine ⟨B, fun a ha => ?_⟩
  obtain ⟨t, htlo, hthi⟩ := exists_between (max_lt ha hsT)
  have hst : s < t := (le_max_right a s).trans_lt htlo
  exact ⟨t, (le_max_left a s).trans_lt htlo, ⟨hs.trans hst.le, hthi⟩,
    hbound t ⟨hst.le, hthi⟩⟩



theorem exists_open_uniform_scalar_tail (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) {x : M} (hx : x ∈ H.reference.regularLimitSet) :
    ∃ (s B : ℝ) (U : Set M), H.reference.tMinus < s ∧ s < T ∧ 0 < B ∧
      IsOpen U ∧ x ∈ U ∧ U ⊆ H.reference.regularLimitSet ∧
        ∀ t ∈ Ico s T, ∀ y ∈ U, H.reference.scalar t y ≤ B := by
  obtain ⟨L, hL⟩ := hx
  let K := max (H.r₀⁻¹ ^ 2) L + 1
  have hrho : 0 < H.r₀⁻¹ ^ 2 := sq_pos_of_pos (inv_pos.mpr H.r₀_pos)
  have hrhoK : H.r₀⁻¹ ^ 2 ≤ K := by dsimp [K]; linarith [le_max_left (H.r₀⁻¹ ^ 2) L]
  have hLK : L < K := by dsimp [K]; linarith [le_max_right (H.r₀⁻¹ ^ 2) L]
  have hK : 0 < K := hrho.trans_le hrhoK
  let delta := 1 / (4 * (H.analytic_constant + 1) * K)
  have hdelta : 0 < delta := by dsimp [delta]; positivity [H.analytic_constant_pos]
  obtain ⟨s, hsnear, hs, hsL⟩ := hL (max H.reference.tMinus (T - delta))
    (max_lt H.reference.tMinus_lt (sub_lt_self T hdelta))
  have hsref : H.reference.tMinus < s := (le_max_left _ _).trans_lt hsnear
  have hmargin : T - s < 1 / (4 * (H.analytic_constant + 1) * K) := by
    have := (le_max_right H.reference.tMinus (T - delta)).trans_lt hsnear
    change T - s < delta
    linarith
  let U : Set M := {y | H.reference.scalar s y < K}
  have hbound : ∀ t ∈ Ico s T, ∀ y ∈ U, H.reference.scalar t y ≤ 2 * K := by
    intro t ht y hy
    exact (SingularRegularLimit.scalar_lt_two_mul_of_short_tail H.analytic_constant_pos.le
      hrho hrhoK ((H.reference_scalar_continuousOn P04 y).mono
        (Ico_subset_Ico_left hsref.le)) hy
      (fun z hz => H.reference_scalar_derivative_bound y z ⟨hsref.trans hz.1, hz.2⟩)
      hmargin t ht).le
  refine ⟨s, 2 * K, U, hsref, hs.2, by positivity,
    isOpen_lt (H.reference_scalar_continuous P04 s hs) continuous_const,
    hsL.trans_lt hLK, ?_, hbound⟩
  intro y hy
  exact H.mem_regularLimitSet_of_scalar_tail hsref.le hs.2 (fun t ht => hbound t ht y hy)


theorem regularLimitSet_isOpen (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) : IsOpen H.reference.regularLimitSet := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨s, B, U, _, _, _, hU, hxU, hsub, _⟩ := H.exists_open_uniform_scalar_tail P04 hx
  exact mem_of_superset (hU.mem_nhds hxU) hsub


theorem regularLimitSet_eventually_bounded (H : SingularTimeAssumptions F T M)
    (P04 : RicciFlowCurvatureTheory.{u}) :
    ∀ x ∈ H.reference.regularLimitSet,
      ∃ B : ℝ, ∃ s : ℝ, H.reference.tMinus ≤ s ∧ s < T ∧
        ∀ t, s < t → t < T → |H.reference.scalar t x| ≤ B := by
  intro x hx
  obtain ⟨s, B, U, hsref, hsT, _, _, hxU, _, hbound⟩ :=
    H.exists_open_uniform_scalar_tail P04 hx
  obtain ⟨L, hL⟩ := H.reference_scalar_lower_bound
  refine ⟨max B (-L), s, hsref.le, hsT, ?_⟩
  intro t hst htT
  apply abs_le.mpr
  constructor
  · have := hL t ⟨hsref.le.trans hst.le, htT⟩ x
    linarith [le_max_right B (-L)]
  · exact (hbound t ⟨hst.le, htT⟩ x hxU).trans (le_max_left _ _)

end PoincareConjecture.SingularTimeAssumptions
