import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.LocalizedCompactness
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Sobolev.Density














set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal

namespace PoincareConjecture

open EuclideanTranslationNative




theorem m64Annulus_l2_isCompact_of_localized
    (f : ℕ → LoopPlane → ℝ)
    (hf : ∀ j, MemLp (f j) 2 (volume.restrict (interior m64AnnulusDomain)))
    {A : ℝ} (hA : ∀ j p, ‖f j p‖ ≤ A)
    (hlocal : ∀ (phi : LoopPlane → ℝ), ContDiff ℝ (⊤ : ℕ∞) phi →
      HasCompactSupport phi → tsupport phi ⊆ interior m64AnnulusDomain →
      ∃ hV : ∀ j, MemLp (fun p => phi p * f j p) 2 volume,
        IsCompact (closure (range (fun j => (hV j).toLp (fun p => phi p * f j p))))) :
    ∃ hU : ∀ j, MemLp ((interior m64AnnulusDomain).indicator (f j)) 2 volume,
      IsCompact (closure (range (fun j => (hU j).toLp
        ((interior m64AnnulusDomain).indicator (f j))))) := by
  let S := interior m64AnnulusDomain
  have hS : MeasurableSet S := isOpen_interior.measurableSet
  have hfinite : volume S ≠ ⊤ :=
    ne_top_of_le_ne_top m64AnnulusDomain_volume_ne_top (measure_mono interior_subset)
  let : IsFiniteMeasure (volume.restrict S) := ⟨by simpa using hfinite.lt_top⟩
  have hA0 : 0 ≤ A := (norm_nonneg (f 0 0)).trans (hA 0 0)
  have hf2 (j : ℕ) (p : LoopPlane) : (f j p) ^ 2 ≤ A ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (sq_le_sq₀ (norm_nonneg (f j p)) hA0).mpr (hA j p)
  have hU (j : ℕ) : MemLp (S.indicator (f j)) 2 volume :=
    (memLp_indicator_iff_restrict hS).mpr (hf j)
  let U (j : ℕ) := (hU j).toLp (S.indicator (f j))
  have hTB : TotallyBounded (range U) := by
    apply Metric.totallyBounded_iff.mpr
    intro epsilon hepsilon
    let delta := (epsilon / 2) ^ 2 / (A ^ 2 + 1)
    have hdelta : 0 < delta := div_pos (sq_pos_of_pos (half_pos hepsilon)) (by positivity)
    obtain ⟨K, hKS, hK, hsmall⟩ := hS.exists_isCompact_sdiff_lt hfinite
      (ENNReal.ofReal_pos.mpr hdelta).ne'
    obtain ⟨rho, phi, -, -, hphi, hc, hrange, hone, hs⟩ :=
      Poincare.Analysis.Sobolev.Euclidean.exists_smooth_cutoff_with_neighborhood
        hK isOpen_interior hKS
    obtain ⟨hV, hcompact⟩ := hlocal phi hphi hc hs
    let V (j : ℕ) := (hV j).toLp (fun p => phi p * f j p)
    have herr (j : ℕ) : dist (U j) (V j) < epsilon / 2 := by
      rw [dist_eq_norm]
      apply (sq_lt_sq₀ (norm_nonneg _) (half_pos hepsilon).le).mp
      let w : LoopPlane → ℝ := fun p => S.indicator (f j) p - phi p * f j p
      have hw : MemLp w 2 volume := (hU j).sub (hV j)
      have houtside (p : LoopPlane) (hp : p ∉ S \ K) : w p = 0 := by
        by_cases hpS : p ∈ S
        · have hpK : p ∈ K := by simpa only [Set.mem_sdiff, hpS, true_and, not_not] using hp
          have hp1 := hone p (Metric.self_subset_cthickening K hpK)
          simp only [w, indicator_of_mem hpS, hp1, one_mul, sub_self]
        · have hp0 : phi p = 0 := image_eq_zero_of_notMem_tsupport (fun h => hpS (hs h))
          simp only [w, indicator_of_notMem hpS, hp0, zero_mul, sub_self]
      have hbound (p : LoopPlane) (hp : p ∈ S \ K) : w p ^ 2 ≤ A ^ 2 := by
        have hp01 := hrange (mem_range_self p)
        have hp1 : (1 - phi p) ^ 2 ≤ 1 := by nlinarith [hp01.1, hp01.2]
        simp only [w, indicator_of_mem hp.1]
        nlinarith [mul_le_mul_of_nonneg_right hp1 (sq_nonneg (f j p)), hf2 j p]
      have hsmallreal : volume.real (S \ K) < delta := ENNReal.toReal_lt_of_lt_ofReal hsmall
      have hdeltaA : delta * A ^ 2 < (epsilon / 2) ^ 2 := by
        dsimp only [delta]
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : 0 < A ^ 2 + 1)]
        nlinarith [sq_pos_of_pos (half_pos hepsilon)]
      calc
        ‖U j - V j‖ ^ 2 = ∫ p, w p ^ 2 := by
          dsimp only [U, V]
          rw [← MemLp.toLp_sub, scalar_toLp_norm_sq]
          rfl
        _ = ∫ p in S \ K, w p ^ 2 := by
          symm
          exact setIntegral_eq_integral_of_forall_compl_eq_zero
            (fun p hp => by rw [houtside p hp]; norm_num)
        _ ≤ ∫ _p in S \ K, A ^ 2 :=
          setIntegral_mono_on hw.integrable_sq.integrableOn
            (integrableOn_const (ne_top_of_le_ne_top hfinite (measure_mono sdiff_subset)))
            (hS.diff hK.measurableSet) hbound
        _ = volume.real (S \ K) * A ^ 2 := by rw [setIntegral_const, smul_eq_mul]
        _ ≤ delta * A ^ 2 := mul_le_mul_of_nonneg_right hsmallreal.le (sq_nonneg A)
        _ < (epsilon / 2) ^ 2 := hdeltaA
    obtain ⟨centers, hcenters, hcover⟩ := Metric.totallyBounded_iff.mp hcompact.totallyBounded
      (epsilon / 2) (half_pos hepsilon)
    refine ⟨centers, hcenters, ?_⟩
    rintro _ ⟨j, rfl⟩
    obtain ⟨v, hv⟩ := mem_iUnion.mp (hcover (subset_closure (mem_range_self j)))
    obtain ⟨hvcenters, hv⟩ := mem_iUnion.mp hv
    apply mem_iUnion.mpr
    refine ⟨v, mem_iUnion.mpr ⟨hvcenters, ?_⟩⟩
    rw [Metric.mem_ball] at hv ⊢
    exact (dist_triangle (U j) (V j) v).trans_lt (by linarith [herr j])
  exact ⟨hU, hTB.closure.isCompact_of_isClosed isClosed_closure⟩




theorem m64Annulus_l2_isCompact
    (f : ℕ → LoopPlane → ℝ) (hf : ∀ j, ContDiff ℝ 1 (f j))
    {A C : ℝ} (hA : ∀ j p, ‖f j p‖ ≤ A)
    (hC : ∀ j (i : Fin 2), (∫ p in interior m64AnnulusDomain,
      (fderiv ℝ (f j) p (EuclideanSpace.single i 1)) ^ 2) ≤ C) :
    ∃ hU : ∀ j, MemLp ((interior m64AnnulusDomain).indicator (f j)) 2 volume,
      IsCompact (closure (range (fun j => (hU j).toLp
        ((interior m64AnnulusDomain).indicator (f j))))) := by
  let S := interior m64AnnulusDomain
  have hfinite : volume S ≠ ⊤ :=
    ne_top_of_le_ne_top m64AnnulusDomain_volume_ne_top (measure_mono interior_subset)
  let : IsFiniteMeasure (volume.restrict S) := ⟨by simpa using hfinite.lt_top⟩
  apply m64Annulus_l2_isCompact_of_localized f
    (fun j => MemLp.of_bound (hf j).continuous.aestronglyMeasurable A
      (Eventually.of_forall (hA j))) hA
  intro phi hphi hc hs
  exact m64Annulus_localized_l2_isCompact f hf hA hC phi (hphi.of_le (by simp)) hc hs

end PoincareConjecture
