import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityMetricBounds
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Topology BigOperators

universe u v

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M] {N : ℕ}
  {α : Type v}

noncomputable def m65EmbeddedEnergyDensity (g : RiemannianMetric 3 M)
    (e : M → EuclideanSpace ℝ (Fin N)) (q : α → M)
    (d : Fin 2 → α → EuclideanSpace ℝ (Fin N)) (z : α) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, m65EmbeddingMetric g e (q z) (d i z) (d i z)

theorem m65EmbeddingMetric_nonneg (g : RiemannianMetric 3 M)
    (e : M → EuclideanSpace ℝ (Fin N)) (p : M) (v : EuclideanSpace ℝ (Fin N)) :
    0 ≤ m65EmbeddingMetric g e p v v := by
  by_cases hv : v = 0
  · simp [hv]
  exact (m65EmbeddingMetric_pos g e p hv).le

theorem m65EmbeddedEnergyDensity_bounds (g : RiemannianMetric 3 M)
    (e : M → EuclideanSpace ℝ (Fin N)) {c C : ℝ}
    (hb : ∀ p (v : EuclideanSpace ℝ (Fin N)),
      c * ‖v‖ ^ 2 ≤ m65EmbeddingMetric g e p v v ∧
        m65EmbeddingMetric g e p v v ≤ C * ‖v‖ ^ 2)
    (q : α → M) (d : Fin 2 → α → EuclideanSpace ℝ (Fin N)) (z : α) :
    (c / 2) * ∑ i, ‖d i z‖ ^ 2 ≤ m65EmbeddedEnergyDensity g e q d z ∧
      m65EmbeddedEnergyDensity g e q d z ≤ (C / 2) * ∑ i, ‖d i z‖ ^ 2 := by
  have hl := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => (hb (q z) (d i z)).1)
  have hu := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => (hb (q z) (d i z)).2)
  simp only [← Finset.mul_sum] at hl hu
  constructor
  · unfold m65EmbeddedEnergyDensity
    nlinarith only [hl]
  · unfold m65EmbeddedEnergyDensity
    nlinarith only [hu]

variable [MeasurableSpace α]

theorem m65EmbeddedEnergyDensity_integrable (g : RiemannianMetric 3 M)
    (e : M → EuclideanSpace ℝ (Fin N)) (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ p, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e p))
    (hemb : Topology.IsEmbedding e) (compact : IsCompact (univ : Set M))
    {μ : Measure α} {q : α → M} {d : Fin 2 → α → EuclideanSpace ℝ (Fin N)}
    (hq : AEStronglyMeasurable (fun z => e (q z)) μ) (hd : ∀ i, MemLp (d i) 2 μ) :
    Integrable (m65EmbeddedEnergyDensity g e q d) μ := by
  let : TopologicalSpace.PseudoMetrizableSpace M := hemb.toIsInducing.pseudoMetrizableSpace
  have hq' : AEStronglyMeasurable q μ := hemb.aestronglyMeasurable_comp_iff.mp hq
  have hH := (m65EmbeddingMetric_contMDiff g e he hinj).continuous
  have hpair : Continuous (fun z : M × EuclideanSpace ℝ (Fin N) =>
      m65EmbeddingMetric g e z.1 z.2 z.2) :=
    ((hH.comp continuous_fst).clm_apply continuous_snd).clm_apply continuous_snd
  obtain ⟨c, C, _, _, hb⟩ := m65EmbeddingMetric_uniform_bounds g e he hinj compact
  have hterm (i : Fin 2) :
      Integrable (fun z => m65EmbeddingMetric g e (q z) (d i z) (d i z)) μ := by
    have hi := (memLp_two_iff_integrable_sq_norm (hd i).1).mp (hd i)
    apply (hi.const_mul C).mono'
      (hpair.comp_aestronglyMeasurable (hq'.prodMk (hd i).1))
    exact ae_of_all _ (fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (m65EmbeddingMetric_nonneg g e (q z) (d i z))]
      exact (hb (q z) (d i z)).2)
  exact (integrable_finsetSum Finset.univ (fun i _ => hterm i)).const_mul (1 / 2 : ℝ)

end PoincareConjecture
