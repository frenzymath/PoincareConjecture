import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Exhaustion.TensorTestBound
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Maximum.MetricSlabBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin n)

theorem exists_raw_tensor_pair_test_slab_bound
    {J I : Set ℝ} (F : RicciFlow n V J) (hI : IsCompact I) (hIJ : I ⊆ J)
    {E : Set V} (hE : IsCompact E)
    (a : ℝ → V → ℝ) (U W : ℝ → V → V)
    (ha : ContinuousOn (Function.uncurry a) (I ×ˢ univ))
    (hU : ContinuousOn (Function.uncurry U) (I ×ˢ univ))
    (hW : ContinuousOn (Function.uncurry W) (I ×ˢ univ))
    (ha0 : ∀ t ∈ I, ∀ x ∉ E, a t x = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ I, ∀ H : V → (Fin 2 → V) → ℝ,
      IsSmoothCovariantTensor H → ∀ δ : ℝ, 0 ≤ δ →
      (∀ x ∈ E, ((F.metric t).tensorNorm H x) ^ 2 ≤ δ ^ 2) →
      |∫ x, a t x * H x ![U t x, W t x]| ≤ C * δ := by
  let weight := fun p : ℝ × V => |a p.1 p.2| *
    ((F.metric p.1).inner p.2 (U p.1 p.2) (U p.1 p.2) +
      (F.metric p.1).inner p.2 (W p.1 p.2) (W p.1 p.2) + 1)
  have hg := (rawMetricBilin_family_contDiffOn F).continuousOn.mono
    (prod_mono hIJ Subset.rfl)
  have hw : ContinuousOn weight (I ×ˢ univ) :=
    ha.abs.mul ((((hg.clm_apply hU).clm_apply hU).add
      ((hg.clm_apply hW).clm_apply hW)).add continuousOn_const)
  obtain ⟨M₀, hM₀⟩ := (hI.prod hE).exists_bound_of_continuousOn
    (hw.mono (prod_mono Subset.rfl (subset_univ E)))
  let M := max 0 M₀
  have hM : 0 ≤ M := le_max_left _ _
  refine ⟨M * volume.real E, mul_nonneg hM ENNReal.toReal_nonneg, ?_⟩
  intro t ht H hH δ hδ hbound
  have hweight (x : V) (hx : x ∈ E) : weight (t, x) ≤ M :=
    (le_abs_self _).trans ((hM₀ (t, x) ⟨ht, hx⟩).trans (le_max_right _ _))
  have hpoint (x : V) (hx : x ∈ E) : ‖a t x * H x ![U t x, W t x]‖ ≤ δ * M := by
    rw [Real.norm_eq_abs, abs_mul]
    have he := mul_le_mul_of_nonneg_left
      (abs_twoTensor_pair_le_of_normSq (F.metric t) hH hδ x (U t x) (W t x) (hbound x hx))
      (abs_nonneg (a t x))
    have he' : |a t x| * |H x ![U t x, W t x]| ≤ δ * weight (t, x) := by
      convert! he using 1
      dsimp only [weight]
      ring
    exact he'.trans (mul_le_mul_of_nonneg_left (hweight x hx) hδ)
  have hs : (∫ x in E, a t x * H x ![U t x, W t x]) =
      ∫ x, a t x * H x ![U t x, W t x] :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by rw [ha0 t ht x hx, zero_mul])
  have hb : ‖∫ x in E, a t x * H x ![U t x, W t x]‖ ≤ (δ * M) * volume.real E :=
    norm_setIntegral_le_of_norm_le_const_ae' hE.measure_lt_top
      (Eventually.of_forall (fun x hx => hpoint x hx))
  rw [hs, Real.norm_eq_abs] at hb
  calc
    _ ≤ (δ * M) * volume.real E := hb
    _ = (M * volume.real E) * δ := by ring

end PoincareConjecture.M35.Uniqueness.Heat
