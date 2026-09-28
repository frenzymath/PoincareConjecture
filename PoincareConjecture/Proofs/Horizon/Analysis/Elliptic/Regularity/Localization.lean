import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.LocalIntegrability
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Sobolev.Weak.Witnesses

noncomputable section

open Set MeasureTheory Function Topology
open scoped ENNReal ContDiff

namespace Poincare.Analysis.Elliptic

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

theorem memLp_mul_of_compact_memLp
    {O : Set E} {u χ : E → ℝ}
    (hu : ∀ K, IsCompact K → K ⊆ O → MemLp u 2 (volume.restrict K))
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hχO : tsupport χ ⊆ O) :
    MemLp (fun x => χ x * u x) 2 volume := by
  have hlocal := compact_memLp_mul_continuousOn hχ.continuousOn hu hχc hχO
  have heq : (tsupport χ).indicator (fun x => χ x * u x) = fun x => χ x * u x := by
    ext x
    by_cases hx : x ∈ tsupport χ
    · simp [hx]
    · simp [hx, image_eq_zero_of_notMem_tsupport hx]
  rw [← heq]
  exact (memLp_indicator_iff_restrict (isClosed_tsupport χ).measurableSet).mpr hlocal

theorem memLp_cutoff_weakPartial
    {O : Set E} {u g χ : E → ℝ} (i : Fin n)
    (hu : ∀ K, IsCompact K → K ⊆ O → MemLp u 2 (volume.restrict K))
    (hg : ∀ K, IsCompact K → K ⊆ O → MemLp g 2 (volume.restrict K))
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχO : tsupport χ ⊆ O) :
    MemLp (fun x => χ x * g x +
      (fderiv ℝ χ x) (EuclideanSpace.single i 1) * u x) 2 volume := by
  apply (memLp_mul_of_compact_memLp hg hχ.continuous hχc hχO).add
  apply memLp_mul_of_compact_memLp hu
    ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const)
    (hχc.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1))
  exact (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)).trans hχO

theorem hasWeakPartialDeriv_cutoff
    {O : Set E} {u g χ : E → ℝ} (i : Fin n)
    (hu : ∀ K, IsCompact K → K ⊆ O → MemLp u 2 (volume.restrict K))
    (hg : ∀ K, IsCompact K → K ⊆ O → MemLp g 2 (volume.restrict K))
    (hweak : Sobolev.Weak.HasWeakPartialDeriv i g u O)
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχO : tsupport χ ⊆ O) :
    Sobolev.Weak.HasWeakPartialDeriv i
      (fun x => χ x * g x + (fderiv ℝ χ x) (EuclideanSpace.single i 1) * u x)
      (fun x => χ x * u x) Set.univ := by
  intro φ hφ hφc _
  let e : E := EuclideanSpace.single i 1
  have hχd : Continuous (fun x => (fderiv ℝ χ x) e) :=
    (hχ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hχdc : HasCompactSupport (fun x => (fderiv ℝ χ x) e) := hχc.fderiv_apply (𝕜 := ℝ) e
  have hχdO : tsupport (fun x => (fderiv ℝ χ x) e) ⊆ O :=
    (tsupport_fderiv_apply_subset ℝ e).trans hχO
  have hχu := memLp_mul_of_compact_memLp hu hχ.continuous hχc hχO
  have hχg := memLp_mul_of_compact_memLp hg hχ.continuous hχc hχO
  have hdχu := memLp_mul_of_compact_memLp hu hχd hχdc hχdO
  have hφd : Continuous (fun x => (fderiv ℝ φ x) e) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hφdc : HasCompactSupport (fun x => (fderiv ℝ φ x) e) := hφc.fderiv_apply (𝕜 := ℝ) e
  have hint1 : Integrable (fun x => (χ x * u x) * (fderiv ℝ φ x) e) := by
    simpa only [smul_eq_mul] using
      hχu.locallyIntegrable (by norm_num) |>.integrable_smul_right_of_hasCompactSupport hφd hφdc
  have hint2 : Integrable (fun x => ((fderiv ℝ χ x) e * u x) * φ x) := by
    simpa only [smul_eq_mul] using
      hdχu.locallyIntegrable (by norm_num) |>.integrable_smul_right_of_hasCompactSupport hφ.continuous hφc
  have hint3 : Integrable (fun x => (χ x * g x) * φ x) := by
    simpa only [smul_eq_mul] using
      hχg.locallyIntegrable (by norm_num) |>.integrable_smul_right_of_hasCompactSupport hφ.continuous hφc
  have hχφO : tsupport (fun x => χ x * φ x) ⊆ O :=
    (tsupport_smul_subset_left χ φ).trans hχO
  have hkey := hweak (fun x => χ x * φ x) (hχ.mul hφ) hχc.mul_right hχφO
  have hprod : ∀ x, (fderiv ℝ (fun y => χ y * φ y) x) e =
      χ x * (fderiv ℝ φ x) e + φ x * (fderiv ℝ χ x) e := by
    intro x
    rw [fderiv_fun_mul (hχ.differentiable (by simp)).differentiableAt
      (hφ.differentiable (by simp)).differentiableAt]
    simp [smul_eq_mul]
  have hz : ∀ x ∉ O, χ x = 0 ∧ (fderiv ℝ χ x) e = 0 := by
    intro x hx
    exact ⟨image_eq_zero_of_notMem_tsupport (fun h => hx (hχO h)),
      image_eq_zero_of_notMem_tsupport (f := fun y => (fderiv ℝ χ y) e)
        (fun h => hx (hχdO h))⟩
  change (∫ x in O, u x * (fderiv ℝ (fun y => χ y * φ y) x) e) = _ at hkey
  simp_rw [hprod] at hkey
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx => by simp [(hz x hx).1, (hz x hx).2]),
    setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx => by simp [(hz x hx).1])] at hkey
  have hleft : (fun x => u x * (χ x * (fderiv ℝ φ x) e + φ x * (fderiv ℝ χ x) e)) =
      fun x => (χ x * u x) * (fderiv ℝ φ x) e + ((fderiv ℝ χ x) e * u x) * φ x := by
    ext x; ring
  have hright : (fun x => g x * (χ x * φ x)) = fun x => (χ x * g x) * φ x := by
    ext x; ring
  rw [hleft, hright, integral_add hint1 hint2] at hkey
  simp only [Measure.restrict_univ]
  change (∫ x, (χ x * u x) * (fderiv ℝ φ x) e) =
    -(∫ x, (χ x * g x + (fderiv ℝ χ x) e * u x) * φ x)
  simp_rw [add_mul]
  rw [integral_add hint3 hint2]
  linarith

theorem memW1p_cutoff
    {O : Set E} {u χ : E → ℝ} {p : Fin n → E → ℝ}
    (hu : ∀ K, IsCompact K → K ⊆ O → MemLp u 2 (volume.restrict K))
    (hp : ∀ i K, IsCompact K → K ⊆ O → MemLp (p i) 2 (volume.restrict K))
    (hweak : ∀ i, Sobolev.Weak.HasWeakPartialDeriv i (p i) u O)
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχO : tsupport χ ⊆ O) :
    Sobolev.Weak.MemW1p 2 (fun x => χ x * u x) Set.univ := by
  refine ⟨?_, fun i => ⟨_, ?_, hasWeakPartialDeriv_cutoff i hu (hp i) (hweak i) hχ hχc hχO⟩⟩
  · simpa only [Measure.restrict_univ] using memLp_mul_of_compact_memLp hu hχ.continuous hχc hχO
  · simpa only [Measure.restrict_univ] using memLp_cutoff_weakPartial i hu (hp i) hχ hχc hχO

theorem cutoff_eqOn_of_eq_one
    {V : Set E} (hV : IsOpen V) {χ u : E → ℝ} {p : Fin n → E → ℝ}
    (hχ : ∀ x ∈ V, χ x = 1) :
    Set.EqOn (fun x => χ x * u x) u V ∧
      ∀ i, Set.EqOn (fun x => χ x * p i x +
        (fderiv ℝ χ x) (EuclideanSpace.single i 1) * u x) (p i) V := by
  refine ⟨fun x hx => by simp [hχ x hx], fun i x hx => ?_⟩
  have heq : χ =ᶠ[𝓝 x] fun _ => (1 : ℝ) :=
    Filter.mem_of_superset (hV.mem_nhds hx) (fun y hy => hχ y hy)
  dsimp only
  rw [Filter.EventuallyEq.fderiv_eq heq]
  simp [hχ x hx]

end Poincare.Analysis.Elliptic
