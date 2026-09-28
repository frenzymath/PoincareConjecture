import PoincareConjecture.Proofs.M35.Thm12_28.CanonicalScalarEstimates
import Mathlib.Order.Filter.AtTopBot.Archimedean










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35



theorem exists_bad_point_with_earlier_control {g₀ : StandardInitialMetric}
    (F : MaximalStandardCapFlow g₀) (Good : ℝ → StandardCapSpace → Prop)
    (H : ℝ) (hH : 0 < H)
    (hbad : ∀ B : ℝ, 0 < B → ∃ t ∈ Ico 0 F.base.lifetime,
      ∃ x : StandardCapSpace, B ≤ (F.connection t).scalarCurvature x ∧
        ¬Good t x) :
    ∃ t ∈ Ico 0 F.base.lifetime, ∃ x : StandardCapSpace,
      H ≤ (F.connection t).scalarCurvature x ∧
      ¬Good t x ∧
      ∀ s ∈ Ico 0 F.base.lifetime, s ≤ t → ∀ y : StandardCapSpace,
        4 * (F.connection t).scalarCurvature x ≤ (F.connection s).scalarCurvature y →
          Good s y := by
  obtain ⟨T, hT, z, hz, hbadz⟩ := hbad (2 * H) (by positivity)
  let S : Set ℝ := {r | ∃ s ∈ Icc 0 T, ∃ y : StandardCapSpace,
    r = (F.connection s).scalarCurvature y ∧
      ¬Good s y}
  have hseed : (F.connection T).scalarCurvature z ∈ S :=
    ⟨T, ⟨hT.1, le_rfl⟩, z, rfl, hbadz⟩
  have hnonempty : S.Nonempty := ⟨_, hseed⟩
  obtain ⟨K, _, hK⟩ := F.base.curvature_locally_bounded T hT.1 hT.2
  have hbounded : BddAbove S := by
    refine ⟨9 * K, ?_⟩
    rintro r ⟨s, hs, y, rfl, _⟩
    have hn := (le_abs_self _).trans (hK s hs y)
    have hscalar := M10.abs_scalarCurvature_le
      (F.base.flow.metric s) (F.base.flow.connection s) y
    norm_num at hscalar
    change |(F.connection s).scalarCurvature y| ≤
      9 * (F.connection s).curvatureTensorNorm y at hscalar
    change (F.connection s).curvatureTensorNorm y ≤ K at hn
    linarith [le_abs_self ((F.connection s).scalarCurvature y)]
  have hsup : 2 * H ≤ sSup S := hz.trans (le_csSup hbounded hseed)
  have hsup_pos : 0 < sSup S := (by positivity : 0 < 2 * H).trans_le hsup
  obtain ⟨r, ⟨t, ht, x, rfl, hbadx⟩, hlarge⟩ :=
    exists_lt_of_lt_csSup hnonempty (half_lt_self hsup_pos)
  have hQ : H ≤ (F.connection t).scalarCurvature x := by linarith
  refine ⟨t, ⟨ht.1, ht.2.trans_lt hT.2⟩, x, hQ, hbadx, ?_⟩
  intro s hs hst y hhigh
  by_contra hbad_y
  have hmem : (F.connection s).scalarCurvature y ∈ S :=
    ⟨s, ⟨hs.1, hst.trans ht.2⟩, y, rfl, hbad_y⟩
  have hupper := le_csSup hbounded hmem
  linarith




theorem exists_first_failure_sequence {g₀ : StandardInitialMetric}
    (F : MaximalStandardCapFlow g₀) (Good : ℝ → StandardCapSpace → Prop)
    (H₀ : ℝ) (hH₀ : 0 < H₀)
    (hbad : ∀ B : ℝ, 0 < B → ∃ t ∈ Ico 0 F.base.lifetime,
      ∃ x : StandardCapSpace, B ≤ (F.connection t).scalarCurvature x ∧
        ¬Good t x) :
    ∃ (t : ℕ → ℝ) (x : ℕ → StandardCapSpace),
      (∀ k, t k ∈ Ico 0 F.base.lifetime) ∧
      (∀ k : ℕ, H₀ + (k : ℝ) ≤ (F.connection (t k)).scalarCurvature (x k)) ∧
      (∀ k, ¬Good (t k) (x k)) ∧
      Tendsto (fun k => (F.connection (t k)).scalarCurvature (x k)) atTop atTop ∧
      ∀ k, ∀ s ∈ Ico 0 F.base.lifetime, s ≤ t k → ∀ y : StandardCapSpace,
        4 * (F.connection (t k)).scalarCurvature (x k) ≤
            (F.connection s).scalarCurvature y →
          Good s y := by
  have hselect (k : ℕ) := exists_bad_point_with_earlier_control
    F Good (H₀ + (k : ℝ)) (by positivity) hbad
  choose t ht x hx hbadx hprior using hselect
  refine ⟨t, x, ht, hx, hbadx, ?_, hprior⟩
  refine tendsto_atTop.2 fun b => ?_
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (b - H₀)]
    with k hk
  linarith [hx k]

end PoincareConjecture.M35
