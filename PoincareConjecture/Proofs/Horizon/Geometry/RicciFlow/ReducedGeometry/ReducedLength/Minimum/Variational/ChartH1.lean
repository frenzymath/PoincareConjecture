import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variational.ChartEnergy












set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped Manifold ContDiff Bundle intervalIntegral ENNReal

universe u

namespace PoincareConjecture.ReducedLengthMinimum.Variational

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem finite_chartH1_limit {ι : Type*} [Fintype ι]
    (g : RiemannianMetric n M) (a b : ι → ℝ) (hab : ∀ i, a i ≤ b i)
    (x : ι → M) (K : ι → Set M) (hK : ∀ i, IsCompact (K i))
    (hsrc : ∀ i, K i ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) (x i)).source)
    (α : ℕ → ℝ → M) (γ : ℝ → M)
    (hα : ∀ i k, ContinuousOn (α k) (Icc (a i) (b i)))
    (hreg : ∀ i k, ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 (α k) (Ioo (a i) (b i)))
    (hαK : ∀ i k, MapsTo (α k) (Icc (a i) (b i)) (K i))
    (hγK : ∀ i, MapsTo γ (Icc (a i) (b i)) (K i))
    (hpoint : ∀ i s, s ∈ Icc (a i) (b i) →
      Tendsto (fun k => α k s) atTop (𝓝 (γ s)))
    (hE : ∀ i k, IntervalIntegrable (referenceSpeedSq g (α k)) volume (a i) (b i))
    (C : ι → ℝ) (hbound : ∀ i k, (∫ s in a i..b i, referenceSpeedSq g (α k) s) ≤ C i) :
    ∃ (v : ∀ i, ℕ → IntervalL2 (EuclideanSpace ℝ (Fin n)) (a i) (b i))
      (w : ∀ i, IntervalL2 (EuclideanSpace ℝ (Fin n)) (a i) (b i))
      (B : ι → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ i k, ‖v i k‖ ≤ B i ∧
        (v i k : ℝ → EuclideanSpace ℝ (Fin n)) =ᵐ[volume.restrict (Icc (a i) (b i))]
          deriv ((extChartAt (𝓡 n) (x i)) ∘ α k)) ∧
      (∀ i, ∀ s ∈ Icc (a i) (b i),
        extChartAt (𝓡 n) (x i) (γ s) = extChartAt (𝓡 n) (x i) (γ (a i)) +
          ∫ r in a i..s, w i r) ∧
      ∀ i, ∀ l : IntervalL2 (EuclideanSpace ℝ (Fin n)) (a i) (b i) →L[ℝ] ℝ,
        Tendsto (fun k => l (v i (φ k))) atTop (𝓝 (l (w i))) := by
  classical
  choose c hc hcbound using fun i => chart_velocity_L2_bound g (x i) (hK i) (hsrc i)
  choose hLp hvbound using fun i k =>
    hcbound i (hab i) (α k) (hreg i k) (hαK i k) (hE i k) (hbound i k)
  let v : ∀ i, ℕ → IntervalL2 (EuclideanSpace ℝ (Fin n)) (a i) (b i) :=
    fun i k => (hLp i k).toLp (deriv ((extChartAt (𝓡 n) (x i)) ∘ α k))
  let : Fact ((2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞)) := ⟨by norm_num⟩
  let (i : ι) : TopologicalSpace.SeparableSpace
      (IntervalL2 (EuclideanSpace ℝ (Fin n)) (a i) (b i)) := inferInstance
  obtain ⟨φ, hφ, w, hweak⟩ := exists_finite_weak_subsequence v
    (fun i => Real.sqrt ((c i)⁻¹ * C i)) hvbound
  refine ⟨v, w, (fun i => Real.sqrt ((c i)⁻¹ * C i)), φ, hφ,
    (fun i k => ⟨hvbound i k, (hLp i k).coeFn_toLp⟩), ?_, fun i => (hweak i).2⟩
  intro i s hs
  apply primitive_of_weak_limit
    (fun k => (extChartAt (𝓡 n) (x i)) ∘ α (φ k))
    ((extChartAt (𝓡 n) (x i)) ∘ γ) (fun k => v i (φ k)) (w i) _ _ (hweak i).2 hs
  · intro k r hr
    have hαsrc : ∀ t ∈ Icc (a i) (b i),
        α (φ k) t ∈ (chartAt (EuclideanSpace ℝ (Fin n)) (x i)).source := by
      intro t ht
      exact (hsrc i) (hαK i (φ k) ht)
    apply primitive_of_deriv
      ((continuousOn_extChartAt (I := 𝓡 n) (x i)).comp (hα i (φ k))
        (fun t ht => by simpa only [extChartAt_source] using hαsrc t ht)) _
      (hLp i (φ k)) hr
    intro t ht
    have hm := ((hreg i (φ k) t ht).contMDiffAt (isOpen_Ioo.mem_nhds ht)).mdifferentiableAt
      (by norm_num)
    exact ((mdifferentiableAt_extChartAt
      (hαsrc t (Ioo_subset_Icc_self ht))).comp t hm).differentiableAt.hasDerivAt
  · intro t ht
    have hsrc' : γ t ∈ (extChartAt (𝓡 n) (x i)).source := by
      simpa only [extChartAt_source] using hsrc i (hγK i ht)
    exact ((continuousAt_extChartAt' hsrc').tendsto.comp
      (hpoint i t ht)).comp hφ.tendsto_atTop

end PoincareConjecture.ReducedLengthMinimum.Variational
