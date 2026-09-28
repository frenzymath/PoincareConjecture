import PoincareConjecture.Proofs.M34.Sec12_5_RotationInvariance.CompatibleEndIntegral
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Set MeasureTheory
open scoped Manifold ContDiff BigOperators

namespace PoincareConjecture.M34

open DifferenceEnergy

theorem exists_compatibleEnd_neighbor_bound
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
      (F : ℕ → RicciFlow 3 (endReferenceRegion e) J)
      (F' : ℕ → RicciFlow 3 (endReferenceRegion e) J')
      (p : endReferenceRegion e) {t : ℝ}, t ∈ J ∩ J' →
      (∀ (i j : ℕ) (r : ℝ), (r = -1 ∨ r = 0 ∨ r = 1) → (i : ℝ) = r + (j : ℝ) →
        ∀ y ∈ endReferenceOverlap e r, ∀ u v : TangentSpace (𝓡 3) y,
          ((F i).metric t).inner y u v =
            ((F j).metric t).inner (endReferenceTransition e p r y)
              (mfderiv (𝓡 3) (𝓡 3) (endReferenceTransition e p r) y u)
              (mfderiv (𝓡 3) (𝓡 3) (endReferenceTransition e p r) y v)) →
      (∀ (i j : ℕ) (r : ℝ), (r = -1 ∨ r = 0 ∨ r = 1) → (i : ℝ) = r + (j : ℝ) →
        ∀ y ∈ endReferenceOverlap e r, ∀ u v : TangentSpace (𝓡 3) y,
          ((F' i).metric t).inner y u v =
            ((F' j).metric t).inner (endReferenceTransition e p r y)
              (mfderiv (𝓡 3) (𝓡 3) (endReferenceTransition e p r) y u)
              (mfderiv (𝓡 3) (𝓡 3) (endReferenceTransition e p r) y v)) →
      let rho := fun j : ℕ => canonicalDifferenceDensity
        (endReferenceRegion e) (endReferenceRegion_isOpen e) qH qA qS (F j) (F' j) p t
      ∀ j : ℕ, (∫ x in tsupport (endEnergyCutoff e), rho (j + 1) x) ≤
        C * ((∫ x, endEnergyCutoff e x ^ 2 * rho j x) +
          (∫ x, endEnergyCutoff e x ^ 2 * rho (j + 1) x) +
          (∫ x, endEnergyCutoff e x ^ 2 * rho (j + 2) x)) := by
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (endReferenceRegion_isOpen e).isOpenEmbedding_subtypeVal.isManifold_singleton
    (I := 𝓡 3) (n := ∞)
  let : MeasurableSpace StandardCapSpace := borel _
  let : BorelSpace StandardCapSpace := ⟨rfl⟩
  let K := endClosedSlab e (31 / 10) (49 / 10)
  have hK : IsCompact K := endClosedSlab_isCompact e (by norm_num)
  have hKU : K ⊆ endReferenceRegion e :=
    endClosedSlab_subset_reference e (by norm_num) (by norm_num)
  have himLow : endAxialTranslation e (-(1 : ℝ)) '' endClosedSlab e (41 / 10) (23 / 5) =
      endClosedSlab e (31 / 10) (18 / 5) := by
    convert endClosedSlab_translation e (a := 41 / 10) (b := 23 / 5) (by norm_num) (-1) using 1
    norm_num
  have himMid : endAxialTranslation e (-(0 : ℝ)) '' endClosedSlab e (17 / 5) (23 / 5) =
      endClosedSlab e (17 / 5) (23 / 5) := by
    simpa using endClosedSlab_translation e (a := 17 / 5) (b := 23 / 5) (by norm_num) 0
  have himHigh : endAxialTranslation e (-(-1 : ℝ)) '' endClosedSlab e (17 / 5) (39 / 10) =
      endClosedSlab e (22 / 5) (49 / 10) := by
    convert endClosedSlab_translation e (a := 17 / 5) (b := 39 / 10) (by norm_num) 1 using 1 <;>
      norm_num
  obtain ⟨Cl, hCl, hl⟩ := exists_compatibleEnd_integral_bound e qH qA qS hK hKU
    (endClosedSlab_isCompact e (a := 41 / 10) (b := 23 / 5) (by norm_num))
    (endClosedSlab_mono e (by norm_num) (by norm_num))
    (r := 1) (Or.inr (Or.inr rfl))
    (by rw [himLow]; exact endClosedSlab_mono e le_rfl (by norm_num))
    (fun x hx => endEnergyCutoff_eq_one_on_slab e
      (endClosedSlab_mono e (by norm_num) le_rfl hx))
  obtain ⟨Cm, hCm, hm⟩ := exists_compatibleEnd_integral_bound e qH qA qS hK hKU
    (endClosedSlab_isCompact e (a := 17 / 5) (b := 23 / 5) (by norm_num))
    (endClosedSlab_mono e (by norm_num) (by norm_num))
    (r := 0) (Or.inr (Or.inl rfl))
    (by rw [himMid]; exact endClosedSlab_mono e (by norm_num) (by norm_num))
    (fun x hx => endEnergyCutoff_eq_one_on_slab e hx)
  obtain ⟨Ch, hCh, hh⟩ := exists_compatibleEnd_integral_bound e qH qA qS hK hKU
    (endClosedSlab_isCompact e (a := 17 / 5) (b := 39 / 10) (by norm_num))
    (endClosedSlab_mono e (by norm_num) (by norm_num))
    (r := -1) (Or.inl rfl)
    (by rw [himHigh]; exact endClosedSlab_mono e (by norm_num) le_rfl)
    (fun x hx => endEnergyCutoff_eq_one_on_slab e
      (endClosedSlab_mono e le_rfl (by norm_num) hx))
  let C := max Cl (max Cm Ch)
  have hClC : Cl ≤ C := le_max_left _ _
  have hCmC : Cm ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hChC : Ch ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C, hCl.trans hClC, ?_⟩
  intro J J' F F' p t ht hF hF' rho j
  have hli : ((j + 1 : ℕ) : ℝ) = 1 + (j : ℝ) := by push_cast; ring
  have hmi : ((j + 1 : ℕ) : ℝ) = 0 + ((j + 1 : ℕ) : ℝ) := by rw [zero_add]
  have hhi : ((j + 1 : ℕ) : ℝ) = -1 + ((j + 2 : ℕ) : ℝ) := by push_cast; ring
  have hlow := hl (F (j + 1)) (F' (j + 1)) (F j) (F' j) p ht ht
    (hF (j + 1) j 1 (Or.inr (Or.inr rfl)) hli)
    (hF' (j + 1) j 1 (Or.inr (Or.inr rfl)) hli)
  have hmid := hm (F (j + 1)) (F' (j + 1)) (F (j + 1)) (F' (j + 1)) p ht ht
    (hF (j + 1) (j + 1) 0 (Or.inr (Or.inl rfl)) hmi)
    (hF' (j + 1) (j + 1) 0 (Or.inr (Or.inl rfl)) hmi)
  have hhigh := hh (F (j + 1)) (F' (j + 1)) (F (j + 2)) (F' (j + 2)) p ht ht
    (hF (j + 1) (j + 2) (-1) (Or.inl rfl) hhi)
    (hF' (j + 1) (j + 2) (-1) (Or.inl rfl) hhi)
  rw [himLow] at hlow
  rw [himMid] at hmid
  rw [himHigh] at hhigh
  let W : Fin 3 → Set StandardCapSpace := ![endClosedSlab e (31 / 10) (18 / 5),
    endClosedSlab e (17 / 5) (23 / 5), endClosedSlab e (22 / 5) (49 / 10)]
  have hW (i : Fin 3) : IsCompact (W i) := by
    fin_cases i <;> exact endClosedSlab_isCompact e (by norm_num)
  have hWU (i : Fin 3) : W i ⊆ endReferenceRegion e := by
    fin_cases i <;> exact endClosedSlab_subset_reference e (by norm_num) (by norm_num)
  have hc : ContinuousOn (rho (j + 1)) (endReferenceRegion e) :=
    canonicalDifferenceDensity_continuousOn_slice _ _ qH qA qS _ _ p ht
  have h0 (k : ℕ) (x : StandardCapSpace) : 0 ≤ rho k x :=
    canonicalDifferenceDensity_nonneg _ _ qH qA qS _ _ p t x
  have hcover : tsupport (endEnergyCutoff e) ⊆ ⋃ i ∈ (Finset.univ : Finset (Fin 3)), W i := by
    intro x hx
    rcases endEnergyCutoff_tsupport_subset_three_slabs e hx with (hlow | hmid) | hhigh
    · exact mem_iUnion.mpr ⟨0, mem_iUnion.mpr ⟨Finset.mem_univ _, hlow⟩⟩
    · exact mem_iUnion.mpr ⟨1, mem_iUnion.mpr ⟨Finset.mem_univ _, hmid⟩⟩
    · exact mem_iUnion.mpr ⟨2, mem_iUnion.mpr ⟨Finset.mem_univ _, hhigh⟩⟩
  have hsum := setIntegral_le_finsetSum_of_cover (μ := volume) Finset.univ
    (isClosed_tsupport (endEnergyCutoff e)).measurableSet (fun i _ => (hW i).measurableSet)
    (ContinuousOn.integrableOn_compact (energyCutoffs_hasCompactSupport e).1
      (hc.mono (endEnergyCutoff_tsupport_subset_region e)))
    (fun i _ => ContinuousOn.integrableOn_compact (hW i) (hc.mono (hWU i))) (h0 (j + 1)) hcover
  have hsupport : (∫ x in tsupport (endEnergyCutoff e), rho (j + 1) x) ≤
      (∫ x in W 0, rho (j + 1) x) + (∫ x in W 1, rho (j + 1) x) +
        (∫ x in W 2, rho (j + 1) x) := by
    simpa only [Fin.sum_univ_three] using hsum
  have hE (k : ℕ) : 0 ≤ ∫ x, endEnergyCutoff e x ^ 2 * rho k x :=
    integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (h0 k x))
  calc
    _ ≤ (∫ x in W 0, rho (j + 1) x) + (∫ x in W 1, rho (j + 1) x) +
        (∫ x in W 2, rho (j + 1) x) := hsupport
    _ ≤ Cl * (∫ x, endEnergyCutoff e x ^ 2 * rho j x) +
        Cm * (∫ x, endEnergyCutoff e x ^ 2 * rho (j + 1) x) +
        Ch * (∫ x, endEnergyCutoff e x ^ 2 * rho (j + 2) x) :=
      add_le_add (add_le_add hlow hmid) hhigh
    _ ≤ C * (∫ x, endEnergyCutoff e x ^ 2 * rho j x) +
        C * (∫ x, endEnergyCutoff e x ^ 2 * rho (j + 1) x) +
        C * (∫ x, endEnergyCutoff e x ^ 2 * rho (j + 2) x) :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_right hClC (hE j))
        (mul_le_mul_of_nonneg_right hCmC (hE (j + 1))))
        (mul_le_mul_of_nonneg_right hChC (hE (j + 2)))
    _ = _ := by ring

end PoincareConjecture.M34
