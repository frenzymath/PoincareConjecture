import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Exhaustion.Spectral
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Kernel.Pointwise.Semigroup
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Regularity.Interior









set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold ContDiff Topology InnerProductSpace BoundedContinuousFunction

namespace PoincareConjecture.LeviCivitaData.Dirichlet

open Boundary Poincare.Analysis.Dirichlet.Kernel

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [PreconnectedSpace M] {g : RiemannianMetric n M}

omit [PreconnectedSpace M] in
theorem memLp_iterate_laplacian_heatKernelContinuous_restrict
    (D : LeviCivitaData g) {Ω : ℕ → Set M}
    (S : ∀ q, Poincare.Manifold.SmoothDomain n (Ω q))
    {V : Set M} (hVm : MeasurableSet V) (q : ℕ) (hV : V ⊆ Ω q)
    (j : ℕ) {t : ℝ} (ht : 0 < t) (y : M) :
    MemLp ((D.laplacian)^[j]
      (fun x => heatKernelContinuousTime D (S q) t x y)) 2
        (g.volumeMeasure.restrict V) := by
  let f := evaluationRow
    (heatPowerContinuous D (S q) 0 (t / 2) (half_pos ht)) y
  have hkernel :
      (fun x => heatKernelContinuousTime D (S q) t x y) =
        heatPowerContinuous D (S q) 0 (t / 2) (half_pos ht) f := by
    funext x
    rw [heatKernelContinuousTime_of_pos D (S q) ht]
    exact heatKernelContinuous_eq_heatPowerContinuous D (S q) t ht x y
  rw [hkernel]
  have heq := iterate_laplacian_heatPowerContinuous
    D (S q) j 0 (t / 2) (half_pos ht) f
  apply (memLp_congr_ae (show ((D.laplacian)^[j]
      (heatPowerContinuous D (S q) 0 (t / 2) (half_pos ht) f : M → ℝ))
        =ᵐ[g.volumeMeasure.restrict V]
      (fun x => (-1 : ℝ) ^ j *
        heatPowerContinuous D (S q) (0 + j) (t / 2) (half_pos ht) f x) from ?_)).mpr
  · exact ((memLp_heatPowerContinuous D (S q) (0 + j) (t / 2) (half_pos ht) f).const_mul
      ((-1 : ℝ) ^ j)).mono_measure (Measure.restrict_mono hV le_rfl)
  · filter_upwards [ae_restrict_mem hVm] with x hx
    exact heq (hV hx)

omit [PreconnectedSpace M] in
theorem eLpNorm_iterate_laplacian_heatKernelContinuous_restrict_le
    (D : LeviCivitaData g) {Ω : ℕ → Set M}
    (S : ∀ q, Poincare.Manifold.SmoothDomain n (Ω q))
    {V : Set M} (hVm : MeasurableSet V) (q : ℕ) (hV : V ⊆ Ω q)
    {a t : ℝ} (ha : 0 < a) (hat : a ≤ t) (j : ℕ) (y : M) :
    (eLpNorm ((D.laplacian)^[j]
      (fun x => heatKernelContinuousTime D (S q) t x y)) 2
        (g.volumeMeasure.restrict V)).toReal ≤
      (((j.factorial : ℝ) / (a / 2) ^ j) *
        ‖evaluationRow (heatPowerContinuous D (S q) 0 (t / 2)
          (half_pos (ha.trans_le hat))) y‖) := by
  have ht : 0 < t := ha.trans_le hat
  have hhalf : 0 < t / 2 := half_pos ht
  have hhalf_lower : a / 2 ≤ t / 2 := by
    exact (div_le_div_of_nonneg_right hat (by norm_num : (0 : ℝ) ≤ 2))
  have hkernel :
      (fun x => heatKernelContinuousTime D (S q) t x y) =
        heatPowerContinuous D (S q) 0 (t / 2) hhalf
          (evaluationRow (heatPowerContinuous D (S q) 0 (t / 2) hhalf) y) := by
    funext x
    rw [heatKernelContinuousTime_of_pos D (S q) ht]
    exact heatKernelContinuous_eq_heatPowerContinuous D (S q) t ht x y
  rw [hkernel]
  simpa only [Nat.zero_add] using
    (eLpNorm_iterate_laplacian_heatPowerContinuous_restrict_le
      D (S q) hVm hV j 0 (half_pos ha) hhalf_lower
        (evaluationRow (heatPowerContinuous D (S q) 0 (t / 2) hhalf) y))

theorem exists_eLpNorm_iterate_laplacian_heatKernelContinuous_exhaustion_bound
    (D : LeviCivitaData g) (hn : 0 < n) (hc : MetricComplete g)
    {k : ℝ} (hk : 0 ≤ k)
    (hRic : ∀ x (v : TangentSpace (𝓡 n) x),
      -k * g.inner x v v ≤ D.ricci x v v)
    {Ω : ℕ → Set M}
    (S : ∀ q, Poincare.Manifold.SmoothDomain n (Ω q))
    (hΩmono : Monotone Ω) (hcover : (⋃ q, Ω q) = univ)
    (O : M) {R : ℝ} (hR : 1 ≤ R) {a b : ℝ} (ha : 0 < a) :
    ∃ B : ℝ, 0 < B ∧ ∀ j q t, t ∈ Icc a b →
      ∀ y, (g.edist O y).toReal ≤ R → ∀ V, MeasurableSet V → V ⊆ Ω q →
        MemLp ((D.laplacian)^[j]
          (fun x => heatKernelContinuousTime D (S q) t x y)) 2
            (g.volumeMeasure.restrict V) ∧
        (eLpNorm ((D.laplacian)^[j]
          (fun x => heatKernelContinuousTime D (S q) t x y)) 2
            (g.volumeMeasure.restrict V)).toReal ≤
              ((j.factorial : ℝ) / (a / 2) ^ j) * B := by
  obtain ⟨B, hB, hbound⟩ :=
    D.exists_evaluationRow_exhaustion_compact_time_bound hn hc hk hRic
      S hΩmono hcover O hR (a := a / 2) (b := b / 2)
        (div_pos ha (by norm_num : (0 : ℝ) < 2))
  refine ⟨B, hB, ?_⟩
  intro j q t ht y hy V hVm hV
  have ht_half : t / 2 ∈ Icc (a / 2) (b / 2) := by
    constructor
    · exact div_le_div_of_nonneg_right ht.1 (by norm_num : (0 : ℝ) ≤ 2)
    · exact div_le_div_of_nonneg_right ht.2 (by norm_num : (0 : ℝ) ≤ 2)
  have hrow := hbound q (t / 2) ht_half y hy
  have hpower := eLpNorm_iterate_laplacian_heatKernelContinuous_restrict_le
    D S hVm q hV ha ht.1 j y
  exact ⟨memLp_iterate_laplacian_heatKernelContinuous_restrict
    D S hVm q hV j (ha.trans_le ht.1) y,
    hpower.trans (mul_le_mul_of_nonneg_left hrow (by positivity))⟩




theorem eventually_eLpNorm_iterate_laplacian_heatKernelContinuous_exhaustion_bound
    (D : LeviCivitaData g) (hn : 0 < n) (hc : MetricComplete g)
    {k : ℝ} (hk : 0 ≤ k)
    (hRic : ∀ x (v : TangentSpace (𝓡 n) x),
      -k * g.inner x v v ≤ D.ricci x v v)
    {Ω : ℕ → Set M}
    (S : ∀ q, Poincare.Manifold.SmoothDomain n (Ω q))
    (hΩmono : Monotone Ω) (hcover : (⋃ q, Ω q) = univ)
    (O : M) {R : ℝ} (hR : 1 ≤ R) {a b : ℝ} (ha : 0 < a)
    {V : Set M} (hVm : MeasurableSet V) (hVc : IsCompact (closure V)) :
    ∀ j, ∃ C : ℝ, 0 < C ∧ ∀ᶠ q in atTop,
      ∀ t, t ∈ Icc a b → ∀ y, (g.edist O y).toReal ≤ R →
        MemLp ((D.laplacian)^[j]
          (fun x => heatKernelContinuousTime D (S q) t x y)) 2
            (g.volumeMeasure.restrict V) ∧
        (eLpNorm ((D.laplacian)^[j]
          (fun x => heatKernelContinuousTime D (S q) t x y)) 2
            (g.volumeMeasure.restrict V)).toReal ≤ C := by
  obtain ⟨B, hB, hbound⟩ :=
    exists_eLpNorm_iterate_laplacian_heatKernelContinuous_exhaustion_bound
      D hn hc hk hRic S hΩmono hcover O hR ha
  obtain ⟨q₀, hq₀⟩ := hVc.elim_directed_cover Ω (fun q => (S q).isOpen)
    (by rw [hcover]; exact subset_univ _) hΩmono.directed_le
  intro j
  refine ⟨((j.factorial : ℝ) / (a / 2) ^ j) * B, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop q₀] with q hq
  intro t ht y hy
  exact hbound j q t ht y hy V hVm
    (subset_closure.trans (hq₀.trans (hΩmono hq)))

end PoincareConjecture.LeviCivitaData.Dirichlet
