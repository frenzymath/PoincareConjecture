import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Exhaustion.Properties
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Monotone
import Mathlib.Topology.Semicontinuity.Basic

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.LeviCivitaData

noncomputable def dirichletExhaustionKernel {M : Type u}
    (K : ℕ → ℝ → M → M → ℝ) (t : ℝ) (x y : M) : ℝ := ⨆ j, K j t x y

namespace DirichletExhaustion

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {D : LeviCivitaData g}
  {Ω : ℕ → Set M} {K : ℕ → ℝ → M → M → ℝ}
  (hK : ∀ j, Dirichlet.IsDirichletHeatKernel D (Ω j) (K j))
  (hmono : ∀ t, 0 < t → ∀ x y, Monotone (fun j => K j t x y))
  (hbdd : ∀ t, 0 < t → ∀ x y, BddAbove (range (fun j => K j t x y)))

include hbdd in
omit [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M] in
theorem le_supremum (j : ℕ) {t : ℝ} (ht : 0 < t) (x y : M) :
    K j t x y ≤ dirichletExhaustionKernel K t x y :=
  le_ciSup (hbdd t ht x y) j

include hmono hbdd in
omit [TopologicalSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M] in
theorem tendsto_supremum {t : ℝ} (ht : 0 < t) (x y : M) :
    Tendsto (fun j => K j t x y) atTop (𝓝 (dirichletExhaustionKernel K t x y)) :=
  tendsto_atTop_ciSup (hmono t ht x y) (hbdd t ht x y)

include hK hbdd in
theorem nonneg {t : ℝ} (ht : 0 < t) (x y : M) :
    0 ≤ dirichletExhaustionKernel K t x y :=
  ((hK 0).nonneg t ht x y).trans (le_supremum hbdd 0 ht x y)

include hK in
theorem symmetric {t : ℝ} (ht : 0 < t) (x y : M) :
    dirichletExhaustionKernel K t x y = dirichletExhaustionKernel K t y x := by
  unfold dirichletExhaustionKernel
  congr 1
  funext j
  exact (hK j).symmetric t ht x y

include hK hbdd in
theorem lowerSemicontinuous :
    LowerSemicontinuous (fun p : (M × M) × Ioi (0 : ℝ) =>
      dirichletExhaustionKernel K p.2 p.1.1 p.1.2) :=
  lowerSemicontinuous_ciSup (fun p => hbdd p.2 p.2.property p.1.1 p.1.2)
    (fun j => (hK j).continuous.lowerSemicontinuous)

include hK hmono hbdd in
theorem mass {t : ℝ} (ht : 0 < t) (x : M) :
    Integrable (dirichletExhaustionKernel K t x) g.volumeMeasure ∧
      (∫ y, dirichletExhaustionKernel K t x y ∂g.volumeMeasure) ≤ 1 :=
  g.integrable_iSup_of_monotone_of_integral_le
    (fun j => (hK j).integrable_ambient ht x)
    (fun j y => (hK j).nonneg t ht x y)
    (hmono t ht x) (hbdd t ht x)
    (fun j => (hK j).integral_ambient_le_one ht x)

include hK hbdd in
theorem positive (hΩmono : Monotone Ω) (hcover : (⋃ j, Ω j) = univ)
    {t : ℝ} (ht : 0 < t) (x y : M) :
    0 < dirichletExhaustionKernel K t x y := by
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover.symm ▸ mem_univ x)
  obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover.symm ▸ mem_univ y)
  exact ((hK (max i j)).positive t ht x (hΩmono (le_max_left i j) hi)
    y (hΩmono (le_max_right i j) hj)).trans_le
      (le_supremum hbdd (max i j) ht x y)

include hK hmono hbdd in
theorem semigroup {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (x y : M) :
    Integrable (fun z => dirichletExhaustionKernel K s x z *
      dirichletExhaustionKernel K t z y) g.volumeMeasure ∧
    dirichletExhaustionKernel K (s + t) x y =
      ∫ z, dirichletExhaustionKernel K s x z *
        dirichletExhaustionKernel K t z y ∂g.volumeMeasure := by
  have hst : 0 < s + t := add_pos hs ht
  have hi (j : ℕ) := ((hK j).semigroup_ambient hs ht x y).1
  have hpos (j : ℕ) (z : M) : 0 ≤ K j s x z * K j t z y :=
    mul_nonneg ((hK j).nonneg s hs x z) ((hK j).nonneg t ht z y)
  have hm (z : M) : Monotone (fun j => K j s x z * K j t z y) := by
    intro i j hij
    exact mul_le_mul (hmono s hs x z hij) (hmono t ht z y hij)
      ((hK i).nonneg t ht z y) ((hK j).nonneg s hs x z)
  have hl (z : M) := (tendsto_supremum hmono hbdd hs x z).mul
    (tendsto_supremum hmono hbdd ht z y)
  have hbound (j : ℕ) : (∫ z, K j s x z * K j t z y ∂g.volumeMeasure) ≤
      dirichletExhaustionKernel K (s + t) x y := by
    rw [← ((hK j).semigroup_ambient hs ht x y).2]
    exact le_supremum hbdd j hst x y
  have hlim := g.integrable_limit_of_monotone_of_integral_le hi hpos hm hl hbound
  refine ⟨hlim.1, ?_⟩
  have hint := integral_tendsto_of_tendsto_of_monotone hi hlim.1
    (ae_of_all _ hm) (ae_of_all _ hl)
  have heq : (fun j => ∫ z, K j s x z * K j t z y ∂g.volumeMeasure) =
      (fun j => K j (s + t) x y) := by
    funext j
    exact ((hK j).semigroup_ambient hs ht x y).2.symm
  rw [heq] at hint
  exact tendsto_nhds_unique (tendsto_supremum hmono hbdd hst x y) hint

end DirichletExhaustion
end PoincareConjecture.LeviCivitaData
