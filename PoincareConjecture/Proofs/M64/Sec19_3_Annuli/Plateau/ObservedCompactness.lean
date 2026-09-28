import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.StrongCompactness
import PoincareConjecture.Proofs.M03.Existence.LpFiniteCoordinatesNative
import PoincareConjecture.Proofs.M03.Existence.FiniteLocalizationCompactnessNative












set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M]



theorem m64Annulus_scalar_observed_l2_isCompact
    (g : RiemannianMetric n M) (e : M → ℝ)
    (he : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) 1 e)
    (f : ℕ → LoopPlane → M) (hf : ∀ j, ContMDiff (𝓡 2) (𝓡 n) 1 (f j))
    {C : ℝ} (hC : ∀ j, (∫ p in interior m64AnnulusDomain,
      m60EnergyDensity g (f j) p) ≤ C) :
    ∃ hU : ∀ j, MemLp ((interior m64AnnulusDomain).indicator (e ∘ f j)) 2 volume,
      IsCompact (closure (range (fun j => (hU j).toLp
        ((interior m64AnnulusDomain).indicator (e ∘ f j))))) := by
  have hu (j : ℕ) : ContDiff ℝ 1 (e ∘ f j) :=
    contMDiff_iff_contDiff.mp (he.comp (hf j))
  obtain ⟨A, hA⟩ := (isCompact_range he.continuous).isBounded.exists_norm_le
  obtain ⟨B, hB0, hB⟩ := M60.exists_observed_derivative_energy_bound g e he
  have hder (j : ℕ) (i : Fin 2) :
      (∫ p in interior m64AnnulusDomain,
        (fderiv ℝ (e ∘ f j) p (EuclideanSpace.single i 1)) ^ 2) ≤ B * C := by
    have hE : IntegrableOn (m60EnergyDensity g (f j)) (interior m64AnnulusDomain) volume :=
      ((m60EnergyDensity_continuous g (hf j)).continuousOn.integrableOn_compact
      m64AnnulusDomain_isCompact).mono_set interior_subset
    have hD : IntegrableOn
        (fun p => (fderiv ℝ (e ∘ f j) p (EuclideanSpace.single i 1)) ^ 2)
        (interior m64AnnulusDomain) volume :=
      ((((hu j).continuous_fderiv (by simp)).clm_apply
      (continuous_const (y := EuclideanSpace.single i 1))).pow 2).continuousOn
      |>.integrableOn_compact m64AnnulusDomain_isCompact |>.mono_set interior_subset
    calc
      _ ≤ ∫ p in interior m64AnnulusDomain, B * m60EnergyDensity g (f j) p := by
        apply integral_mono_ae hD (hE.const_mul B)
        exact Eventually.of_forall fun p => by
          simpa only [EuclideanSpace.basisFun_apply, Real.norm_eq_abs, sq_abs] using
            hB (f j) (hf j) p i
      _ = B * ∫ p in interior m64AnnulusDomain, m60EnergyDensity g (f j) p :=
        integral_const_mul _ _
      _ ≤ B * C := mul_le_mul_of_nonneg_left (hC j) hB0
  exact m64Annulus_l2_isCompact (fun j => e ∘ f j) hu
    (fun _ _ => hA _ (mem_range_self _)) hder




theorem m64Annulus_observed_l2_isCompact {m : ℕ}
    (g : RiemannianMetric n M) (e : M → EuclideanSpace ℝ (Fin m))
    (he : ContMDiff (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 1 e)
    (f : ℕ → LoopPlane → M) (hf : ∀ j, ContMDiff (𝓡 2) (𝓡 n) 1 (f j))
    {C : ℝ} (hC : ∀ j, (∫ p in interior m64AnnulusDomain,
      m60EnergyDensity g (f j) p) ≤ C) :
    ∃ hU : ∀ j, MemLp ((interior m64AnnulusDomain).indicator (e ∘ f j)) 2 volume,
      IsCompact (closure (range (fun j => (hU j).toLp
        ((interior m64AnnulusDomain).indicator (e ∘ f j))))) := by
  classical
  let S := interior m64AnnulusDomain
  have hS : MeasurableSet S := isOpen_interior.measurableSet
  have hfinite : volume S ≠ ⊤ :=
    ne_top_of_le_ne_top m64AnnulusDomain_volume_ne_top (measure_mono interior_subset)
  let : IsFiniteMeasure (volume.restrict S) := ⟨by simpa using hfinite.lt_top⟩
  obtain ⟨A, hA⟩ := (isCompact_range he.continuous).isBounded.exists_norm_le
  have hU (j : ℕ) : MemLp (S.indicator (e ∘ f j)) 2 volume :=
    (memLp_indicator_iff_restrict hS).mpr
      (MemLp.of_bound (he.continuous.comp (hf j).continuous).aestronglyMeasurable A
        (Eventually.of_forall fun p => hA _ (mem_range_self _)))
  have hc (i : Fin m) := m64Annulus_scalar_observed_l2_isCompact g (fun x => e x i)
    ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.contMDiff.comp he) f hf hC
  choose hcoord hcompact using hc
  have heq (i : Fin m) (j : ℕ) :
      LpFiniteCoordinatesNative.coordinateLp volume i ((hU j).toLp (S.indicator (e ∘ f j))) =
        (hcoord i j).toLp (S.indicator (fun p => e (f j p) i)) := by
    apply Lp.ext
    filter_upwards [LpFiniteCoordinatesNative.coordinateLp_toLp_coe volume i (hU j),
      (hcoord i j).coeFn_toLp] with p hp hq
    change ((hcoord i j).toLp (S.indicator (fun p => e (f j p) i))) p =
      S.indicator (fun p => e (f j p) i) p at hq
    rw [hp, hq]
    by_cases hpS : p ∈ S <;> simp [hpS]
  refine ⟨hU, FiniteLocalizationCompactnessNative.isCompact_closure_of_finite_reconstruction
    (fun i v => LpFiniteCoordinatesNative.coordinateLp volume i v)
    (fun i => LpFiniteCoordinatesNative.insertionLp volume i) ?_ ?_⟩
  · intro i
    apply (hcompact i).totallyBounded.subset
    rintro _ ⟨v, ⟨j, rfl⟩, rfl⟩
    exact subset_closure ⟨j, (heq i j).symm⟩
  · intro v _
    exact LpFiniteCoordinatesNative.sum_insertion_coordinate volume v




theorem m64Annulus_observed_strong_subsequence {m : ℕ}
    (g : RiemannianMetric n M) (e : M → EuclideanSpace ℝ (Fin m))
    (he : ContMDiff (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 1 e)
    (f : ℕ → LoopPlane → M) (hf : ∀ j, ContMDiff (𝓡 2) (𝓡 n) 1 (f j))
    {C : ℝ} (hC : ∀ j, (∫ p in interior m64AnnulusDomain,
      m60EnergyDensity g (f j) p) ≤ C) :
    ∃ (hU : ∀ j, MemLp ((interior m64AnnulusDomain).indicator (e ∘ f j)) 2 volume)
      (u : Lp (EuclideanSpace ℝ (Fin m)) 2 (volume : Measure LoopPlane)) (k : ℕ → ℕ),
      StrictMono k ∧ Tendsto (fun j => (hU (k j)).toLp
        ((interior m64AnnulusDomain).indicator (e ∘ f (k j)))) atTop (𝓝 u) := by
  obtain ⟨hU, hc⟩ := m64Annulus_observed_l2_isCompact g e he f hf hC
  obtain ⟨u, -, k, hk, hu⟩ := hc.isSeqCompact (fun j => subset_closure (mem_range_self j))
  exact ⟨hU, u, k, hk, hu⟩

end PoincareConjecture
