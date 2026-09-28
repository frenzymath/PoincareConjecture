import PoincareConjecture.Proofs.M34.Sec12_5_RotationInvariance.CoreImageIntegral
import PoincareConjecture.Proofs.M34.Sec12_5_RotationInvariance.CoreSlabCover
import Mathlib.Algebra.BigOperators.Fin











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set MeasureTheory
open scoped Manifold ContDiff BigOperators

namespace PoincareConjecture.M34

open DifferenceEnergy




theorem exists_coreBand_integral_bound
    {g : RiemannianMetric 3 StandardCapSpace} (e : StandardCylindricalEnd g)
    {dH dA dS : ℕ} (qH : FH 3 ≃L[ℝ] EuclideanSpace ℝ (Fin dH))
    (qA : FA 3 ≃L[ℝ] EuclideanSpace ℝ (Fin dA))
    (qS : FS 3 ≃L[ℝ] EuclideanSpace ℝ (Fin dS)) :
    letI := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
      (I := 𝓡 3) (n := ∞)
    letI : MeasurableSpace StandardCapSpace := borel _
    letI : BorelSpace StandardCapSpace := ⟨rfl⟩
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {J J' : Set ℝ}
      (F : RicciFlow 3 StandardCapSpace J) (F' : RicciFlow 3 StandardCapSpace J')
      (p : endReferenceRegion e) {t : ℝ}, t ∈ J ∩ J' →
      let dc := actualDifferenceEnergyDensity qH qA qS (F.connection t) (F'.connection t)
      let rho := fun j : ℕ => canonicalDifferenceDensity
        (endReferenceRegion e) (endReferenceRegion_isOpen e) qH qA qS
        (endPullbackFlow e F j (by have := Nat.cast_nonneg (α := ℝ) j; linarith))
        (endPullbackFlow e F' j (by have := Nat.cast_nonneg (α := ℝ) j; linarith)) p t
      (∫ x in {x | endExhaustion e x ≤ 6}, dc x) ≤
        C * ((∫ x, coreEnergyCutoff e x ^ 2 * dc x) +
          (∫ x, endEnergyCutoff e x ^ 2 * rho 0 x) +
          (∫ x, endEnergyCutoff e x ^ 2 * rho 1 x)) := by
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
    (I := 𝓡 3) (n := ∞)
  let : MeasurableSpace StandardCapSpace := borel _
  let : BorelSpace StandardCapSpace := ⟨rfl⟩
  obtain ⟨C0, hC0, h0⟩ := exists_coreImage_integral_bound e qH qA qS 0 (by norm_num)
    (endClosedSlab_isCompact e (a := 4) (b := 23 / 5) (by norm_num))
    (endClosedSlab_subset_reference e (by norm_num) (by norm_num))
    (fun x hx => endEnergyCutoff_eq_one_on_slab e
      (endClosedSlab_mono e (by norm_num) le_rfl hx))
  obtain ⟨C1, hC1, h1⟩ := exists_coreImage_integral_bound e qH qA qS 1 (by norm_num)
    (endClosedSlab_isCompact e (a := 17 / 5) (b := 4) (by norm_num))
    (endClosedSlab_subset_reference e (by norm_num) (by norm_num))
    (fun x hx => endEnergyCutoff_eq_one_on_slab e
      (endClosedSlab_mono e le_rfl (by norm_num) hx))
  let C := max 1 (max C0 C1)
  have h1C : 1 ≤ C := le_max_left _ _
  have h0C : C0 ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCC : C1 ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C, zero_le_one.trans h1C, ?_⟩
  intro J J' F F' p t ht dc rho
  have hc : Continuous dc := actualDifferenceEnergyDensity_continuous_euclidean qH qA qS F F' ht
  have hd0 (x) : 0 ≤ dc x := actualDifferenceEnergyDensity_nonneg qH qA qS _ _ x
  have hr0 (j : ℕ) (x : StandardCapSpace) : 0 ≤ rho j x :=
    canonicalDifferenceDensity_nonneg _ _ qH qA qS _ _ p t x
  have hwc : HasCompactSupport (fun x => coreEnergyCutoff e x ^ 2) :=
    (energyCutoffs_hasCompactSupport e).2.comp_left (g := fun r : ℝ => r ^ 2) (by simp)
  have hweighted : Integrable (fun x => coreEnergyCutoff e x ^ 2 * dc x) :=
    integrable_cutoff_mul isOpen_univ ((energyCutoffs_contDiff e).2.continuous.pow 2).continuousOn
      hwc (subset_univ _) hc.continuousOn
  have hcore := setIntegral_le_cutoff_sq_integral
    (endExhaustion_sublevel_isCompact e 5).measurableSet hweighted hd0
    (fun x hx => coreEnergyCutoff_eq_one e hx)
  have him0 : endAxialTranslation e 0 '' endClosedSlab e 4 (23 / 5) =
      endClosedSlab e 4 (23 / 5) := by
    simpa using endClosedSlab_translation e (a := 4) (b := 23 / 5) (by norm_num) 0
  have him1 : endAxialTranslation e 1 '' endClosedSlab e (17 / 5) 4 =
      endClosedSlab e (22 / 5) 5 := by
    convert endClosedSlab_translation e (a := 17 / 5) (b := 4) (by norm_num) 1 using 1
    norm_num
  have he0 := h0 F F' p ht
  have he1 := h1 F F' p ht
  simp only [him0] at he0
  simp only [him1] at he1
  let W : Fin 3 → Set StandardCapSpace := ![{x | endExhaustion e x ≤ 5},
    endClosedSlab e 4 (23 / 5), endClosedSlab e (22 / 5) 5]
  have hW (i : Fin 3) : IsCompact (W i) := by
    fin_cases i
    · exact endExhaustion_sublevel_isCompact e 5
    · exact endClosedSlab_isCompact e (by norm_num)
    · exact endClosedSlab_isCompact e (by norm_num)
  have hcover : {x | endExhaustion e x ≤ 6} ⊆
      ⋃ i ∈ (Finset.univ : Finset (Fin 3)), W i := by
    intro x hx
    rcases endExhaustion_six_sublevel_cover e hx with (hc | h0) | h1
    · exact mem_iUnion.mpr ⟨0, mem_iUnion.mpr ⟨Finset.mem_univ _, hc⟩⟩
    · exact mem_iUnion.mpr ⟨1, mem_iUnion.mpr ⟨Finset.mem_univ _, h0⟩⟩
    · exact mem_iUnion.mpr ⟨2, mem_iUnion.mpr ⟨Finset.mem_univ _, h1⟩⟩
  have hsum := setIntegral_le_finsetSum_of_cover (μ := volume) Finset.univ
    (endExhaustion_sublevel_isCompact e 6).measurableSet (fun i _ => (hW i).measurableSet)
    (ContinuousOn.integrableOn_compact (endExhaustion_sublevel_isCompact e 6) hc.continuousOn)
    (fun i _ => ContinuousOn.integrableOn_compact (hW i) hc.continuousOn) hd0 hcover
  have hE0 : 0 ≤ ∫ x, coreEnergyCutoff e x ^ 2 * dc x :=
    integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (hd0 x))
  have hE (j : ℕ) : 0 ≤ ∫ x, endEnergyCutoff e x ^ 2 * rho j x :=
    integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (hr0 j x))
  calc
    _ ≤ (∫ x in W 0, dc x) + (∫ x in W 1, dc x) + (∫ x in W 2, dc x) := by
      simpa only [Fin.sum_univ_three] using hsum
    _ ≤ (∫ x, coreEnergyCutoff e x ^ 2 * dc x) +
        C0 * (∫ x, endEnergyCutoff e x ^ 2 * rho 0 x) +
        C1 * (∫ x, endEnergyCutoff e x ^ 2 * rho 1 x) :=
      add_le_add (add_le_add hcore (by simpa [W, dc, rho] using he0))
        (by simpa [W, dc, rho] using he1)
    _ ≤ C * (∫ x, coreEnergyCutoff e x ^ 2 * dc x) +
        C * (∫ x, endEnergyCutoff e x ^ 2 * rho 0 x) +
        C * (∫ x, endEnergyCutoff e x ^ 2 * rho 1 x) :=
      add_le_add (add_le_add (by simpa using mul_le_mul_of_nonneg_right h1C hE0)
        (mul_le_mul_of_nonneg_right h0C (hE 0))) (mul_le_mul_of_nonneg_right hCC (hE 1))
    _ = _ := by ring

end PoincareConjecture.M34
