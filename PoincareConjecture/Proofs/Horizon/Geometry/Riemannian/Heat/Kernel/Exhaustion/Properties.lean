import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Exhaustion.Dirichlet

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.LeviCivitaData.Dirichlet.IsDirichletHeatKernel

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {D : LeviCivitaData g}
  {Ω : Set M} {K : ℝ → M → M → ℝ} (hK : IsDirichletHeatKernel D Ω K)

include hK

theorem integrable_ambient {t : ℝ} (ht : 0 < t) (x : M) :
    Integrable (K t x) g.volumeMeasure :=
  IntegrableOn.integrable_of_forall_notMem_eq_zero (hK.mass t ht x).1
    (fun y hy => hK.zero_outside t ht x y (Or.inr hy))

theorem integral_ambient_le_one {t : ℝ} (ht : 0 < t) (x : M) :
    (∫ y, K t x y ∂g.volumeMeasure) ≤ 1 := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := Ω) (fun y hy => hK.zero_outside t ht x y (Or.inr hy))]
  exact (hK.mass t ht x).2

theorem semigroup_ambient {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (x y : M) :
    Integrable (fun z => K s x z * K t z y) g.volumeMeasure ∧
      K (s + t) x y = ∫ z, K s x z * K t z y ∂g.volumeMeasure := by
  have hz (z : M) (hz : z ∉ Ω) : K s x z * K t z y = 0 := by
    rw [hK.zero_outside s hs x z (Or.inr hz), zero_mul]
  obtain ⟨hi, he⟩ := hK.semigroup s t hs ht x y
  exact ⟨IntegrableOn.integrable_of_forall_notMem_eq_zero hi hz,
    he.trans (setIntegral_eq_integral_of_forall_compl_eq_zero hz)⟩

theorem integral_sq_row {t : ℝ} (ht : 0 < t) (x : M) :
    Integrable (fun z => K t x z ^ 2) g.volumeMeasure ∧
      (∫ z, K t x z ^ 2 ∂g.volumeMeasure) = K (2 * t) x x := by
  have he : (fun z => K t x z * K t z x) = (fun z => K t x z ^ 2) := by
    funext z
    rw [hK.symmetric t ht z x, pow_two]
  obtain ⟨hi, hv⟩ := hK.semigroup_ambient ht ht x x
  rw [he] at hi hv
  exact ⟨hi, by simpa only [two_mul] using hv.symm⟩

theorem tendsto_integral_ambient_initial {φ : M → ℝ}
    (hφ : ContinuousOn φ (closure Ω)) {x : M} (hx : x ∈ Ω) :
    Tendsto (fun t => ∫ y, K t x y * φ y ∂g.volumeMeasure)
      (𝓝[>] 0) (𝓝 (φ x)) := by
  apply (hK.initial φ hφ x hx).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by
    rw [hK.zero_outside t ht x y (Or.inr hy), zero_mul]

end PoincareConjecture.LeviCivitaData.Dirichlet.IsDirichletHeatKernel
