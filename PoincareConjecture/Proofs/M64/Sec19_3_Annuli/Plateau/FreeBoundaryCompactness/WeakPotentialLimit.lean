import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.RectangleNormalization
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.HilbertExtraction
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakDerivativeClosure

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal

namespace PoincareConjecture.M64

open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.WeakCompactness

local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S
local notation "b" => fun i : Fin 2 => EuclideanSpace.single i (1 : ℝ)

theorem exists_weak_potential_of_smooth_gradient_limit
    {O : Set LoopPlane} (hO : IsOpen O)
    (F : ℕ → LoopPlane → ℝ) (hF : ∀ j, ContDiffOn ℝ 1 (F j) O)
    (J : Fin 2 → LoopPlane → ℝ) (hJ : ∀ i, MemLp (J i) 2 (volume.restrict O))
    (D : ℕ → Fin 2 → LoopPlane → ℝ)
    (hD : ∀ j i, MemLp (D j i) 2 (volume.restrict O))
    (hderiv : ∀ j i p, D j i p = fderiv ℝ (F j) p (b i))
    {R : ℝ}
    (c : ℕ → ℝ) (hU : ∀ j, MemLp (fun p => F j p - c j) 2 (volume.restrict O))
    (hbound : ∀ j, ‖(hU j).toLp (fun p => F j p - c j)‖ ≤ R)
    (hlim : ∀ i, Tendsto (fun j => eLpNorm (D j i - J i) 2
      (volume.restrict O)) atTop (𝓝 0)) :
    ∃ u : Lp ℝ 2 (volume.restrict O),
      ∀ i : Fin 2, HasWeakPartialDeriv i (J i) u O := by
  classical
  let : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  have hstrong (i : Fin 2) : Tendsto (fun j => (hD j i).toLp (D j i))
      atTop (𝓝 ((hJ i).toLp (J i))) := by
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ (fun j => hD j i) _ (hJ i)).mpr
    exact hlim i
  have hweaksub : ∃ U : Lp ℝ 2 (volume.restrict O), ∃ k : ℕ → ℕ,
      StrictMono k ∧ WeakConverges
        (fun j => (hU (k j)).toLp (fun p => F (k j) p - c (k j))) U := by
    obtain ⟨U, k, hk, hweak⟩ := m64SeparableHilbert_weak_subsequence
      (fun j => (hU j).toLp (fun p => F j p - c j))
      hbound
    exact ⟨U, k, hk, hweak⟩
  obtain ⟨U, k, hk, hweak⟩ := hweaksub
  refine ⟨U, ?_⟩
  intro i
  have hdf (j : ℕ) : MemLp
      (fun p => fderiv ℝ (fun q => F (k j) q - c (k j)) p (b i)) 2
        (volume.restrict O) := by
    have heq : (fun p => fderiv ℝ (fun q => F (k j) q - c (k j)) p (b i)) = D (k j) i := by
      funext p
      rw [fderiv_sub_const]
      exact (hderiv (k j) i p).symm
    rw [heq]
    exact hD (k j) i
  have hfd (j : ℕ) : ContDiffOn ℝ 1
      (fun p => F (k j) p - c (k j)) O :=
    (hF (k j)).sub contDiffOn_const
  have hwD : WeakConverges
      (fun j => (hdf j).toLp
        (fun p => fderiv ℝ (fun q => F (k j) q - c (k j)) p (b i)))
      ((hJ i).toLp (J i)) := by
    have ht : Tendsto
        (fun j => (hdf j).toLp
          (fun p => fderiv ℝ (fun q => F (k j) q - c (k j)) p (b i)))
        atTop (𝓝 ((hJ i).toLp (J i))) := by
      have hcomp := (hstrong i).comp hk.tendsto_atTop
      apply hcomp.congr'
      exact Eventually.of_forall (fun j => by
        have heq : (fun p => fderiv ℝ (fun q => F (k j) q - c (k j)) p (b i)) =
            D (k j) i := by
          funext p
          rw [fderiv_sub_const]
          exact (hderiv (k j) i p).symm
        simp only [Function.comp_apply, heq])
    exact fun L => (L.continuous.tendsto _).comp ht
  have hweakJ : HasWeakPartialDeriv i ((hJ i).toLp (J i)) U O := by
    intro phi hp hpc hps
    have h := distributional_identity_of_weak_limits hO
      (fun j => fun p => F (k j) p - c (k j)) hfd (b i)
      (fun j => hU (k j)) hdf hweak hwD hp hpc hps
    simp only [smul_eq_mul] at h
    have hn := congrArg Neg.neg h
    simp only [neg_neg] at hn
    simpa only [mul_comm] using hn.symm
  exact m64WeakPartialDeriv_ae_congr (EventuallyEq.rfl) (hJ i).coeFn_toLp hweakJ

private theorem scalar_toLp_norm_sq (u : LoopPlane → ℝ) (hu : MemLp u 2 mu) :
    ‖hu.toLp u‖ ^ 2 = ∫ p in S, (u p) ^ 2 := by
  rw [LpFiniteCoordinatesNative.l2_norm_sq]
  apply integral_congr_ae
  filter_upwards [hu.coeFn_toLp] with p hp
  simp only [hp, Real.norm_eq_abs, sq_abs]

theorem annulus_exists_weak_potential_of_smooth_gradient_limit
    (F : ℕ → LoopPlane → ℝ) (hF : ∀ j, ContDiff ℝ 1 (F j))
    (J : Fin 2 → LoopPlane → ℝ) (hJ : ∀ i, MemLp (J i) 2 mu)
    (hlim : ∀ i, Tendsto (fun j => eLpNorm
      (fun p => fderiv ℝ (F j) p (b i) - J i p) 2 mu) atTop (𝓝 0)) :
    ∃ u : LoopPlane → ℝ, MemLp u 2 mu ∧
      ∀ i : Fin 2, HasWeakPartialDeriv i (J i) u S := by
  classical
  let : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  let D := fun (j : ℕ) (i : Fin 2) (p : LoopPlane) => fderiv ℝ (F j) p (b i)
  have hmem (u : LoopPlane → ℝ) (hu : Continuous u) : MemLp u 2 mu := by
    apply (memLp_two_iff_integrable_sq hu.aestronglyMeasurable).mpr
    exact (hu.pow 2).continuousOn.integrableOn_compact m64AnnulusDomain_isCompact
      |>.mono_set interior_subset
  have hD (j : ℕ) (i : Fin 2) : MemLp (D j i) 2 mu :=
    hmem _ (((hF j).continuous_fderiv (by norm_num)).clm_apply continuous_const)
  have hstrong (i : Fin 2) : Tendsto (fun j => (hD j i).toLp (D j i))
      atTop (𝓝 ((hJ i).toLp (J i))) := by
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ (fun j => hD j i) _ (hJ i)).mpr
    change Tendsto (fun j => eLpNorm (D j i - J i) 2 mu) atTop (𝓝 0)
    convert hlim i using 1
    rfl
  have hbounded (i : Fin 2) : ∃ C : ℝ, ∀ j, ‖(hD j i).toLp (D j i)‖ ≤ C := by
    obtain ⟨C, hC⟩ := (hstrong i).cauchySeq.isBounded_range.exists_norm_le
    exact ⟨C, fun j => hC _ (mem_range_self j)⟩
  choose C hC using hbounded
  have hCpos (i : Fin 2) : 0 ≤ C i := (norm_nonneg _).trans (hC i 0)
  choose c hc using fun j => annulus_exists_energy_controlled_normalization (F j) (hF j)
  let f := fun j p => F j p - c j
  have hf (j : ℕ) : ContDiff ℝ 1 (f j) := (hF j).sub contDiff_const
  have hu (j : ℕ) : MemLp (f j) 2 mu := hmem _ (hf j).continuous
  let R := 8 * curvePeriod ^ 2 * (C 0) ^ 2 + 8 * (C 1) ^ 2
  have hbound (j : ℕ) : ‖(hu j).toLp (f j)‖ ^ 2 ≤ R := by
    rw [scalar_toLp_norm_sq]
    apply (hc j).trans
    rw [← scalar_toLp_norm_sq (D j 0) (hD j 0),
      ← scalar_toLp_norm_sq (D j 1) (hD j 1)]
    dsimp [R]
    gcongr
    · exact hC 0 j
    · exact hC 1 j
  obtain ⟨U, k, hk, hweak⟩ := m64SeparableHilbert_weak_subsequence
    (fun j => (hu j).toLp (f j)) (fun j => Real.le_sqrt_of_sq_le (hbound j))
  refine ⟨U, Lp.memLp U, ?_⟩
  intro i
  have hd (j : ℕ) : (fun p => fderiv ℝ (f (k j)) p (b i)) = D (k j) i := by
    funext p
    exact congrArg (fun L : LoopPlane →L[ℝ] ℝ => L (b i)) (fderiv_sub_const (c (k j)))
  have hdf (j : ℕ) : MemLp (fun p => fderiv ℝ (f (k j)) p (b i)) 2 mu := by
    rw [hd]
    exact hD (k j) i
  have hwD : WeakConverges
      (fun j => (hdf j).toLp (fun p => fderiv ℝ (f (k j)) p (b i)))
      ((hJ i).toLp (J i)) := by
    have ht : Tendsto
        (fun j => (hdf j).toLp (fun p => fderiv ℝ (f (k j)) p (b i)))
        atTop (𝓝 ((hJ i).toLp (J i))) := by
      simpa only [hd, Function.comp_def] using (hstrong i).comp hk.tendsto_atTop
    exact fun L => (L.continuous.tendsto _).comp ht
  have hweakJ : HasWeakPartialDeriv i ((hJ i).toLp (J i)) U S := by
    intro phi hp hpc hps
    have h := distributional_identity_of_weak_limits isOpen_interior
      (fun j => f (k j)) (fun j => (hf (k j)).contDiffOn) (b i)
      (fun j => hu (k j)) hdf hweak hwD hp hpc hps
    simp only [smul_eq_mul] at h
    have hn := congrArg Neg.neg h
    simp only [neg_neg] at hn
    simpa only [mul_comm] using hn.symm
  exact m64WeakPartialDeriv_ae_congr (EventuallyEq.rfl) (hJ i).coeFn_toLp hweakJ

end PoincareConjecture.M64
