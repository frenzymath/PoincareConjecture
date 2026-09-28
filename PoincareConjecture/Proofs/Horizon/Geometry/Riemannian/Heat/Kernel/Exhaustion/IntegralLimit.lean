import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Exhaustion.Supremum
import Mathlib.MeasureTheory.Integral.Prod









set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.LeviCivitaData.DirichletExhaustion

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {D : LeviCivitaData g}
  {Ω : ℕ → Set M} {K : ℕ → ℝ → M → M → ℝ}
  (hK : ∀ j, Dirichlet.IsDirichletHeatKernel D (Ω j) (K j))
  (hmono : ∀ t, 0 < t → ∀ x y, Monotone (fun j => K j t x y))
  (hbdd : ∀ t, 0 < t → ∀ x y, BddAbove (range (fun j => K j t x y)))

include hK hmono hbdd


theorem tendsto_setIntegral_supremum (B : Set M) {t : ℝ} (ht : 0 < t) (x : M) :
    Tendsto (fun j => ∫ y in B, K j t x y ∂g.volumeMeasure) atTop
      (𝓝 (∫ y in B, dirichletExhaustionKernel K t x y ∂g.volumeMeasure)) := by
  exact integral_tendsto_of_tendsto_of_monotone
    (fun j => ((hK j).integrable_ambient ht x).integrableOn)
    ((mass hK hmono hbdd ht x).1.integrableOn)
    (ae_of_all _ (hmono t ht x))
    (ae_of_all _ (fun y => tendsto_supremum hmono hbdd ht x y))



theorem integrableOn_integral_supremum_and_tendsto
    [PreconnectedSpace M] {A B : Set M} (hA : g.volumeMeasure A < ⊤)
    (hB : g.volumeMeasure B < ⊤)
    {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun z => ∫ w in B, dirichletExhaustionKernel K t z w
      ∂g.volumeMeasure) A g.volumeMeasure ∧
    Tendsto (fun j => ∫ z in A, ∫ w in B, K j t z w
      ∂g.volumeMeasure ∂g.volumeMeasure) atTop
      (𝓝 (∫ z in A, ∫ w in B, dirichletExhaustionKernel K t z w
        ∂g.volumeMeasure ∂g.volumeMeasure)) := by
  let : SecondCountableTopology M := g.secondCountableTopology
  let : IsFiniteMeasure (g.volumeMeasure.restrict B) := ⟨by simpa using hB⟩
  have hm (j : ℕ) : AEStronglyMeasurable
      (fun z => ∫ w in B, K j t z w ∂g.volumeMeasure) (g.volumeMeasure.restrict A) := by
    have hc0 := (hK j).continuous.comp
      ((continuous_fst.prodMk continuous_snd).prodMk (continuous_const (y := ⟨t, ht⟩)))
    have hc : Continuous (fun p : M × M => K j t p.1 p.2) := by
      apply hc0.congr
      intro p
      rfl
    exact hc.measurable.stronglyMeasurable.integral_prod_right.aestronglyMeasurable
  have hl (z : M) := tendsto_setIntegral_supremum hK hmono hbdd B ht z
  have hUm : AEStronglyMeasurable
      (fun z => ∫ w in B, dirichletExhaustionKernel K t z w ∂g.volumeMeasure)
      (g.volumeMeasure.restrict A) :=
    aestronglyMeasurable_of_tendsto_ae atTop hm (ae_of_all _ hl)
  have hbound (j : ℕ) (z : M) : ‖∫ w in B, K j t z w ∂g.volumeMeasure‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg ((hK j).nonneg t ht z))]
    exact (setIntegral_le_integral ((hK j).integrable_ambient ht z)
      (ae_of_all _ ((hK j).nonneg t ht z))).trans ((hK j).integral_ambient_le_one ht z)
  have hUbound (z : M) :
      ‖∫ w in B, dirichletExhaustionKernel K t z w ∂g.volumeMeasure‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (nonneg hK hbdd ht z))]
    exact (setIntegral_le_integral (mass hK hmono hbdd ht z).1
      (ae_of_all _ (nonneg hK hbdd ht z))).trans (mass hK hmono hbdd ht z).2
  have hconst : IntegrableOn (fun _ : M => (1 : ℝ)) A g.volumeMeasure :=
    integrableOn_const hA.ne
  exact ⟨hconst.mono' hUm (ae_of_all _ hUbound),
    tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) hm hconst
      (fun j => ae_of_all _ (hbound j)) (ae_of_all _ hl)⟩



theorem setIntegral_setIntegral_le_of_uniform_bound
    [PreconnectedSpace M] {A B : Set M} (hA : g.volumeMeasure A < ⊤)
    (hB : g.volumeMeasure B < ⊤)
    {t C : ℝ} (ht : 0 < t)
    (hbound : ∀ j, (∫ z in A, ∫ w in B, K j t z w
      ∂g.volumeMeasure ∂g.volumeMeasure) ≤ C) :
    (∫ z in A, ∫ w in B, dirichletExhaustionKernel K t z w
      ∂g.volumeMeasure ∂g.volumeMeasure) ≤ C := by
  exact le_of_tendsto' (integrableOn_integral_supremum_and_tendsto
    hK hmono hbdd hA hB ht).2 hbound

end PoincareConjecture.LeviCivitaData.DirichletExhaustion
