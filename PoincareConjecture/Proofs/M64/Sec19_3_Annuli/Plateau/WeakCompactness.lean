import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Infimum
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.SUAlphaEnergy
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.Integrability
import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.WeakCompactness.DerivativeLimit

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem m64Annulus_observed_weak_subsequence
    (g : RiemannianMetric n M) (e : M → F)
    (he : ContMDiff (𝓡 n) 𝓘(ℝ, F) 1 e)
    (f : ℕ → LoopPlane → M)
    (hf : ∀ j, ContMDiff (𝓡 2) (𝓡 n) 1 (f j))
    {C : ℝ} (hC : ∀ j, (∫ p in interior m64AnnulusDomain,
      m60EnergyDensity g (f j) p) ≤ C) :
    ∃ (hU : ∀ j, MemLp (e ∘ f j) 2 (volume.restrict (interior m64AnnulusDomain)))
      (hV : ∀ j i, MemLp (fun p => fderiv ℝ (e ∘ f j) p
        (EuclideanSpace.basisFun (Fin 2) ℝ i)) 2
          (volume.restrict (interior m64AnnulusDomain)))
      (u : Lp F 2 (volume.restrict (interior m64AnnulusDomain)))
      (V : Fin 2 → Lp F 2 (volume.restrict (interior m64AnnulusDomain)))
      (k : ℕ → ℕ),
      StrictMono k ∧
      Poincare.Analysis.Sobolev.WeakCompactness.WeakConverges
        (fun j => (hU (k j)).toLp (e ∘ f (k j))) u ∧
      (∀ i, Poincare.Analysis.Sobolev.WeakCompactness.WeakConverges
        (fun j => (hV (k j) i).toLp (fun p => fderiv ℝ (e ∘ f (k j)) p
          (EuclideanSpace.basisFun (Fin 2) ℝ i))) (V i)) ∧
      (∀ i (phi : LoopPlane → ℝ), ContDiff ℝ ∞ phi → HasCompactSupport phi →
        tsupport phi ⊆ interior m64AnnulusDomain →
        (∫ p in interior m64AnnulusDomain, phi p • V i p) =
          -(∫ p in interior m64AnnulusDomain,
            fderiv ℝ phi p (EuclideanSpace.basisFun (Fin 2) ℝ i) • u p)) ∧
      (∑ i, ‖V i‖ ^ 2) ≤ liminf (fun j => ∑ i,
        ‖(hV (k j) i).toLp (fun p => fderiv ℝ (e ∘ f (k j)) p
          (EuclideanSpace.basisFun (Fin 2) ℝ i))‖ ^ 2) atTop := by
  let S := interior m64AnnulusDomain
  let mu := volume.restrict S
  let : IsFiniteMeasure mu := ⟨by
    change volume.restrict S univ < ⊤
    rw [Measure.restrict_apply_univ]
    exact lt_of_le_of_lt (measure_mono interior_subset)
      m64AnnulusDomain_volume_ne_top.lt_top⟩
  have hu (j : ℕ) : ContDiff ℝ 1 (e ∘ f j) :=
    contMDiff_iff_contDiff.mp (he.comp (hf j))
  obtain ⟨A, hA⟩ := (isCompact_range he.continuous).isBounded.exists_norm_le
  have hA0 : 0 ≤ A :=
    (norm_nonneg (e (f 0 0))).trans (hA _ (mem_range_self _))
  have hU (j : ℕ) : MemLp (e ∘ f j) 2 mu :=
    MemLp.of_bound (hu j).continuous.aestronglyMeasurable A
      (Eventually.of_forall fun p => hA _ (mem_range_self _))
  have hUnorm (j : ℕ) : ‖(hU j).toLp (e ∘ f j)‖ ≤
      (measureUnivNNReal mu : ℝ) ^ (2 : ℝ≥0∞).toReal⁻¹ * A := by
    apply Lp.norm_le_of_ae_bound hA0
    filter_upwards [(hU j).coeFn_toLp] with p hp
    rw [hp]
    exact hA _ (mem_range_self _)
  have hE (j : ℕ) : IntegrableOn (m60EnergyDensity g (f j)) S :=
    ((m60EnergyDensity_continuous g (hf j)).continuousOn.integrableOn_compact
      m64AnnulusDomain_isCompact).mono_set interior_subset
  have hD (j : ℕ) (i : Fin 2) : IntegrableOn
      (fun p => ‖fderiv ℝ (e ∘ f j) p
        (EuclideanSpace.basisFun (Fin 2) ℝ i)‖ ^ 2) S :=
    ((((hu j).continuous_fderiv (by simp)).clm_apply continuous_const).norm.pow 2).continuousOn
      |>.integrableOn_compact m64AnnulusDomain_isCompact |>.mono_set interior_subset
  have hV (j : ℕ) (i : Fin 2) : MemLp (fun p => fderiv ℝ (e ∘ f j) p
      (EuclideanSpace.basisFun (Fin 2) ℝ i)) 2 mu :=
    (memLp_two_iff_integrable_sq_norm
      (((hu j).continuous_fderiv (by simp)).clm_apply continuous_const).aestronglyMeasurable).mpr
        (hD j i)
  obtain ⟨B, hB0, hB⟩ := M60.exists_observed_derivative_energy_bound g e he
  have hVnorm (j : ℕ) (i : Fin 2) :
      ‖(hV j i).toLp (fun p => fderiv ℝ (e ∘ f j) p
        (EuclideanSpace.basisFun (Fin 2) ℝ i))‖ ^ 2 ≤ B * C := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
    calc
      _ = ∫ p in S, ‖fderiv ℝ (e ∘ f j) p
          (EuclideanSpace.basisFun (Fin 2) ℝ i)‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards [(hV j i).coeFn_toLp] with p hp
        rw [hp]
      _ ≤ ∫ p in S, B * m60EnergyDensity g (f j) p :=
        integral_mono_ae (hD j i) ((hE j).const_mul B)
          (Eventually.of_forall fun p => hB (f j) (hf j) p i)
      _ = B * ∫ p in S, m60EnergyDensity g (f j) p := integral_const_mul _ _
      _ ≤ B * C := mul_le_mul_of_nonneg_left (hC j) hB0
  obtain ⟨u, V, k, hk, huweak, hVweak, htest, hliminf, -⟩ :=
    Poincare.Analysis.Sobolev.WeakCompactness.weak_w12_subsequence isOpen_interior
      (fun j => e ∘ f j) (fun j => (hu j).contDiffOn)
      (EuclideanSpace.basisFun (Fin 2) ℝ) hU hV hUnorm
      (B := 2 * (B * C)) (fun j => by
        rw [Fin.sum_univ_two]
        linarith [hVnorm j 0, hVnorm j 1])
  exact ⟨hU, hV, u, V, k, hk, huweak, hVweak, htest, hliminf⟩

end PoincareConjecture
