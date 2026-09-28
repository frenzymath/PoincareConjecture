import PoincareConjecture.Proofs.M04.CompactParabolic
import PoincareConjecture.Statements.Ch04.CurvatureTheory
import PoincareConjecture.Definitions.Ch11.BlowupLimits

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M30

theorem exists_earlier_scalar_le
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [CompactSpace M]
    (hC : RicciFlowCurvatureTheory.{u})
    {J : Set ℝ} (F : RicciFlow n M J)
    {a b : ℝ} (hab : a ≤ b) (hJ : Icc a b ⊆ J) (p : M) :
    ∃ x : M, (F.connection a).scalarCurvature x ≤
      (F.connection b).scalarCurvature p := by
  by_cases heq : a = b
  · subst b
    exact ⟨p, le_rfl⟩
  have hpos : 0 < b - a := sub_pos.mpr (lt_of_le_of_ne hab heq)
  have hreg := hC.scalar_regular n M J F
  have hsmooth (t : ℝ) (ht : t ∈ J) :
      ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (F.connection t).scalarCurvature := by
    have hc : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun _ : M => t) := contMDiff_const
    have hi : ContMDiff (𝓡 n) (𝓡 n) ∞ (fun x : M => x) := contMDiff_id
    exact ContMDiffOn.comp_contMDiff (I := 𝓡 n)
      (I' := 𝓘(ℝ, ℝ).prod (𝓡 n)) (I'' := 𝓘(ℝ, ℝ))
      (f := fun x : M => (t, x))
      (g := fun q : ℝ × M => (F.connection q.1).scalarCurvature q.2)
      hreg (hc.prodMk hi) (fun x => ⟨ht, mem_univ x⟩)
  have haJ : a ∈ J := hJ ⟨le_rfl, hab⟩
  obtain ⟨x₀, _hx₀, hmin⟩ := isCompact_univ.exists_isMinOn
    (show (univ : Set M).Nonempty from ⟨p, mem_univ p⟩)
    (hsmooth a haJ).continuous.continuousOn
  let m := (F.connection a).scalarCurvature x₀
  let f : ℝ → M → ℝ := fun s x => (F.connection (a + s)).scalarCurvature x - m
  let v : ℝ → M → ℝ := fun s x =>
    (F.connection (a + s)).laplacian (F.connection (a + s)).scalarCurvature x +
      2 * (F.connection (a + s)).ricciNormSq x
  have hmap : MapsTo (fun s : ℝ => a + s) (Icc 0 (b - a)) J := by
    intro s hs
    apply hJ
    constructor <;> linarith [hs.1, hs.2]
  have hclock : Continuous (fun q : ℝ × M => (a + q.1, q.2)) :=
    (continuous_const.add continuous_fst).prodMk continuous_snd
  have hf : ContinuousOn (Function.uncurry f) (Icc 0 (b - a) ×ˢ (univ : Set M)) :=
    (hreg.continuousOn.comp hclock.continuousOn
      (fun q hq => ⟨hmap hq.1, mem_univ q.2⟩)).sub continuousOn_const
  have hderiv : ∀ s ∈ Icc 0 (b - a), ∀ x : M,
      HasDerivWithinAt (fun r => f r x) (v s x) (Icc 0 (b - a)) s := by
    intro s hs x
    have hc : HasDerivWithinAt (fun r : ℝ => a + r) 1 (Icc 0 (b - a)) s :=
      ((hasDerivAt_id s).const_add a).hasDerivWithinAt
    simpa only [Function.comp_def, mul_one] using
      ((hC.scalar_evolution n M J F (a + s) (hmap hs) x).comp s hc hmap).sub_const m
  have hvelocity : ∀ s ∈ Ioc 0 (b - a), ∀ x : M,
      (∀ y : M, f s x ≤ f s y) → f s x ≤ 0 → -0 * f s x ≤ v s x := by
    intro s hs x hminx _hneg
    have hlocal : IsLocalMin (F.connection (a + s)).scalarCurvature x := by
      apply Filter.Eventually.of_forall
      intro y
      exact (sub_le_sub_iff_right m).mp (hminx y)
    have hlap := (F.connection (a + s)).laplacian_nonneg_of_isLocalMin
      (hsmooth (a + s) (hmap ⟨hs.1.le, hs.2⟩)).contMDiffAt hlocal
    have hricci : 0 ≤ (F.connection (a + s)).ricciNormSq x := by
      exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
    dsimp only [v]
    linarith
  have hinit (x : M) : 0 ≤ f 0 x := by
    change 0 ≤ (F.connection (a + 0)).scalarCurvature x - m
    rw [add_zero]
    exact sub_nonneg.mpr (hmin (mem_univ x))
  have hfinal := M04.compact_min_velocity_nonnegative (K := 0) hpos f v
    hf hderiv hvelocity hinit (b - a) ⟨hpos.le, le_rfl⟩ p
  refine ⟨x₀, ?_⟩
  have hclockEnd : a + (b - a) = b := by ring
  change 0 ≤ (F.connection (a + (b - a))).scalarCurvature p -
    (F.connection a).scalarCurvature x₀ at hfinal
  rw [hclockEnd] at hfinal
  exact sub_nonneg.mp hfinal

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold

theorem exists_compact_limit_scalar_anchor
    (hC : RicciFlowCurvatureTheory.{u})
    {T : ℝ} (L : BlowupLimitFlow.{u} (Ioc (-T) 0))
    [CompactSpace L.carrier.carrier] :
    ∀ t ∈ Ioc (-T) 0, ∃ x : L.carrier.carrier,
      (L.flow.connection t).scalarCurvature x ≤ 1 := by
  intro t ht
  obtain ⟨x, hx⟩ := exists_earlier_scalar_le hC L.flow ht.2
    (fun s hs => ⟨ht.1.trans_le hs.1, hs.2⟩) L.base
  exact ⟨x, L.scalar_normalized ▸ hx⟩

end PoincareConjecture.M30
