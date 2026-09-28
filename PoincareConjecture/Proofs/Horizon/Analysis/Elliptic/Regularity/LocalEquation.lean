import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Coefficients
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Localization

noncomputable section

open Set MeasureTheory Function Topology
open scoped ENNReal ContDiff BigOperators

namespace Poincare.Analysis.Elliptic

open Sobolev.Weak Sobolev.NirenbergEuclidean

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

theorem memLp_continuous_mul_of_hasCompactSupport
    {a v : E → ℝ} (ha : Continuous a) (hv : MemLp v 2 volume)
    (hvc : HasCompactSupport v) : MemLp (fun x => a x * v x) 2 volume := by
  have hlocal := compact_memLp_mul_continuousOn (O := univ) ha.continuousOn
    (fun K _ _ => hv.restrict K) hvc (subset_univ _)
  have heq : (tsupport v).indicator (fun x => a x * v x) = fun x => a x * v x := by
    ext x
    by_cases hx : x ∈ tsupport v
    · simp [hx]
    · simp [hx, image_eq_zero_of_notMem_tsupport hx]
  rw [← heq]
  exact (memLp_indicator_iff_restrict (isClosed_tsupport v).measurableSet).mpr hlocal

theorem weakEquation_congr_restrict
    {O V : Set E} (hVO : V ⊆ O)
    {A a : E → Matrix (Fin n) (Fin n) ℝ} {p q : Fin n → E → ℝ} {f : E → ℝ}
    (ha : EqOn a A V) (hp : ∀ i, EqOn (q i) (p i) V)
    (heq : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ O →
      (∫ x in O, ∑ i, ∑ j, A x i j * p j x *
        fderiv ℝ φ x (EuclideanSpace.single i 1)) = ∫ x in O, f x * φ x) :
    ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ V →
      (∫ x in V, ∑ i, (∑ j, a x i j * q j x) *
        fderiv ℝ φ x (EuclideanSpace.single i 1)) = ∫ x in V, f x * φ x := by
  intro φ hφ hφc hφV
  have hderivzero : ∀ i x, x ∉ V →
      fderiv ℝ φ x (EuclideanSpace.single i 1) = 0 := by
    intro i x hx
    apply image_eq_zero_of_notMem_tsupport
      (f := fun y => fderiv ℝ φ y (EuclideanSpace.single i 1))
    exact fun h => hx (hφV (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1) h))
  have hφzero : ∀ x, x ∉ V → φ x = 0 :=
    fun x hx => image_eq_zero_of_notMem_tsupport (fun h => hx (hφV h))
  have hraw := heq φ hφ hφc (hφV.trans hVO)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx => by simp [hderivzero _ x (fun hv => hx (hVO hv))]),
    setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx => by simp [hφzero x (fun hv => hx (hVO hv))])] at hraw
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx => by simp [hderivzero _ x hx]),
    setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx => by simp [hφzero x hx]), ← hraw]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ V
  · simp only [ha hx, hp _ hx, Finset.sum_mul]
  · simp [hderivzero _ x hx]

theorem exists_localized_weakEquation [NeZero n]
    {O : Set E} (hO : IsOpen O) (A : E → Matrix (Fin n) (Fin n) ℝ)
    (u f : E → ℝ) (p : Fin n → E → ℝ)
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun x => A x i j) O)
    (hpos : ∀ x ∈ O, (A x).PosDef)
    (hu : ∀ K, IsCompact K → K ⊆ O → MemLp u 2 (volume.restrict K))
    (hp : ∀ i K, IsCompact K → K ⊆ O → MemLp (p i) 2 (volume.restrict K))
    (hf : ∀ K, IsCompact K → K ⊆ O → MemLp f 2 (volume.restrict K))
    (hpartial : ∀ i φ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ O →
      (∫ x in O, u x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        -(∫ x in O, p i x * φ x))
    (heq : ∀ φ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ O →
      (∫ x in O, ∑ i, ∑ j, A x i j * p j x *
        fderiv ℝ φ x (EuclideanSpace.single i 1)) = ∫ x in O, f x * φ x)
    {x : E} (hx : x ∈ O) :
    ∃ (V : Set E) (B : SmoothEllipticBilinearForm n univ)
      (u₀ : E → ℝ) (p₀ : Fin n → E → ℝ),
      IsOpen V ∧ x ∈ V ∧ IsCompact (closure V) ∧ closure V ⊆ O ∧
      EqOn B.a A V ∧ EqOn u₀ u V ∧ (∀ i, EqOn (p₀ i) (p i) V) ∧
      HasCompactSupport u₀ ∧ (∀ i, HasCompactSupport (p₀ i)) ∧
      MemLp u₀ 2 volume ∧ (∀ i, MemLp (p₀ i) 2 volume) ∧
      (∀ i, HasWeakPartialDeriv i (p₀ i) u₀ univ) ∧
      (∀ i, MemLp (fun y => ∑ j, B.a y i j * p₀ j y) 2 volume) ∧
      MemLp f 2 (volume.restrict V) ∧
      (∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ V →
        (∫ y in V, ∑ i, (∑ j, B.a y i j * p₀ j y) *
          fderiv ℝ φ y (EuclideanSpace.single i 1)) = ∫ y in V, f y * φ y) := by
  obtain ⟨V, hV, hxV, hVc, hVO, B, hBA, _⟩ :=
    exists_global_elliptic_extension hO (isCompact_singleton (x := x))
      (singleton_subset_iff.mpr hx) A (fun _ => 0) hA hpos contDiffOn_const
  obtain ⟨χ, hχ, hχc, _, hχone, hχO⟩ :=
    SmoothEllipticBilinearForm.exists_cutoff hVc hO hVO
  let u₀ : E → ℝ := fun y => χ y * u y
  let p₀ : Fin n → E → ℝ := fun i y => χ y * p i y +
    (fderiv ℝ χ y) (EuclideanSpace.single i 1) * u y
  have heqOn := cutoff_eqOn_of_eq_one (u := u) (p := p) hV
    (fun y hy => hχone y (subset_closure hy))
  have hp₀c (i : Fin n) : HasCompactSupport (p₀ i) :=
    hχc.mul_right.add (hχc.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)).mul_right
  have hp₀ (i : Fin n) : MemLp (p₀ i) 2 volume :=
    memLp_cutoff_weakPartial i hu (hp i) hχ hχc hχO
  refine ⟨V, B, u₀, p₀, hV, hxV (mem_singleton x), hVc, hVO, hBA,
    heqOn.1, heqOn.2, hχc.mul_right, hp₀c,
    memLp_mul_of_compact_memLp hu hχ.continuous hχc hχO, hp₀, ?_, ?_, ?_, ?_⟩
  · intro i
    exact hasWeakPartialDeriv_cutoff i hu (hp i) (hpartial i) hχ hχc hχO
  · intro i
    exact memLp_finsetSum _ (fun j _ =>
      memLp_continuous_mul_of_hasCompactSupport (B.continuous_a i j) (hp₀ j) (hp₀c j))
  · exact (hf (closure V) hVc hVO).mono_measure (Measure.restrict_mono subset_closure le_rfl)
  · exact weakEquation_congr_restrict (subset_closure.trans hVO) hBA heqOn.2 heq

end Poincare.Analysis.Elliptic
