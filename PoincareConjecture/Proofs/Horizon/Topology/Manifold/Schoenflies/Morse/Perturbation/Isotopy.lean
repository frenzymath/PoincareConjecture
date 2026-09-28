import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Perturbation.Graph
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.Morse.SignedSquares
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Analysis.SpecialFunctions.SmoothTransition









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]



theorem exists_pos_forall_cutoff_translation_isotopy [CompleteSpace E]
    {χ : E -> Real} (hχ : ContDiff Real ∞ χ) (hχc : HasCompactSupport χ) :
    ∃ δ > 0, ∀ a : E, ‖a‖ < δ ->
      ∃ F : Real -> Diffeomorph 𝓘(Real, E) 𝓘(Real, E) E E ∞,
        (∀ x, F 0 x = x) ∧
        ContDiff Real ∞ (fun z : Real × E => F z.1 z.2) ∧
        (∀ s x, x ∉ tsupport χ -> F s x = x) ∧
        ∀ s x, F s x = x + χ x • (Real.smoothTransition s • a) := by
  obtain ⟨δ, hδ, htranslation⟩ := exists_pos_forall_cutoff_translation_homeomorph hχ hχc
  refine ⟨δ, hδ, fun a ha => ?_⟩
  have hsmall (s : Real) : ‖Real.smoothTransition s • a‖ < δ := by
    calc
      _ = Real.smoothTransition s * ‖a‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg s)]
      _ ≤ 1 * ‖a‖ := mul_le_mul_of_nonneg_right (Real.smoothTransition.le_one s) (norm_nonneg a)
      _ < δ := by simpa using ha
  choose e he hes hei heone hefix using fun s => htranslation _ (hsmall s)
  let F (s : Real) : Diffeomorph 𝓘(Real, E) 𝓘(Real, E) E E ∞ := {
    toEquiv := (e s).toEquiv
    contMDiff_toFun := (hes s).contMDiff
    contMDiff_invFun := (hei s).contMDiff }
  have hF (s : Real) (x : E) : F s x = x + χ x • (Real.smoothTransition s • a) := he s x
  refine ⟨F, ?_, ?_, hefix, hF⟩
  · intro x
    simp [hF, Real.smoothTransition.zero]
  · have heq : (fun z : Real × E => F z.1 z.2) =
        (fun z : Real × E => z.2 + χ z.2 • (Real.smoothTransition z.1 • a)) :=
      funext fun z => hF z.1 z.2
    rw [heq]
    exact contDiff_snd.add ((hχ.comp contDiff_snd).smul
      ((Real.smoothTransition.contDiff.comp contDiff_fst).smul contDiff_const))




theorem exists_supported_zero_section_height_shift [FiniteDimensional Real E]
    {h : E -> Real} (hh : ContDiff Real ∞ h) (p : E)
    {r R S ε : Real} (hr : 0 < r) (hrR : r < R) (hS : 0 < S) (hε : 0 < ε)
    (hregular : ∀ x ∈ closedBall p R \ ball p r, fderiv Real h x ≠ 0)
    {A : Set Real} (hA : A.Finite) :
    ∃ (b : E -> Real) (a : Real)
        (F : Real -> Diffeomorph 𝓘(Real, E × Real) 𝓘(Real, E × Real)
          (E × Real) (E × Real) ∞),
      ContDiff Real ∞ b ∧ tsupport b ⊆ closedBall p R ∧
      EqOn b 1 (closedBall p r) ∧ |a| < ε ∧
      (∀ z, F 0 z = z) ∧
      ContDiff Real ∞ (fun z : Real × (E × Real) => F z.1 z.2) ∧
      (∀ s z, z ∉ closedBall p R ×ˢ closedBall (0 : Real) S -> F s z = z) ∧
      (∀ s x, F s (x, 0) = (x, Real.smoothTransition s * a * b x)) ∧
      (∀ s x, fderiv Real
        (fun y => h y + (Real.smoothTransition s * a) * b y) x = 0 ↔
          fderiv Real h x = 0) ∧ h p + a ∉ A := by
  obtain ⟨b, hb, hbc, hbone, hbR, δ, hδ, hshift⟩ :=
    exists_bump_preserving_critical_points hh p hr hrR hregular
  let ρ : ContDiffBump (0 : Real) := ⟨S / 2, S, half_pos hS, half_lt_self hS⟩
  let χ : E × Real -> Real := fun z => b z.1 * ρ z.2
  have hχ : ContDiff Real ∞ χ := (hb.comp contDiff_fst).mul (ρ.contDiff.comp contDiff_snd)
  let K := closedBall p R ×ˢ closedBall (0 : Real) S
  have hK : IsCompact K := (isCompact_closedBall p R).prod (isCompact_closedBall 0 S)
  have hsupp : Function.support χ ⊆ K := by
    rintro ⟨x, z⟩ hxz
    constructor
    · by_contra hx
      have hbzero : b x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hbR h))
      exact hxz (by simp [χ, hbzero])
    · by_contra hz
      have hρzero : ρ z = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        rwa [ρ.tsupport_eq]
      exact hxz (by simp [χ, hρzero])
  have hχK : tsupport χ ⊆ K := closure_minimal hsupp hK.isClosed
  have hχc : HasCompactSupport χ := HasCompactSupport.of_support_subset_isCompact hK hsupp
  obtain ⟨α, hα, hisotopy⟩ := exists_pos_forall_cutoff_translation_isotopy hχ hχc
  let η := min ε (min δ α)
  have hη : 0 < η := lt_min hε (lt_min hδ hα)
  obtain ⟨a, ha, haA⟩ := (Ioo_infinite (show -η < η by linarith)).exists_notMem_finite
    (hA.image (fun c => c - h p))
  have haη : |a| < η := abs_lt.mpr ha
  have haδ : |a| < δ := haη.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have haα : |a| < α := haη.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨F, hF0, hFs, hFfix, hF⟩ := hisotopy (0, a) (by simpa using haα)
  refine ⟨b, a, F, hb, hbR, hbone, haη.trans_le (min_le_left _ _), hF0, hFs,
    ?_, ?_, ?_, ?_⟩
  · intro s z hz
    exact hFfix s z (fun h => hz (hχK h))
  · intro s x
    rw [hF]
    have hρzero : ρ 0 = 1 := ρ.one_of_mem_closedBall (mem_closedBall_self (half_pos hS).le)
    simp [χ, hρzero, mul_comm, mul_left_comm]
  · intro s x
    apply (hshift (Real.smoothTransition s * a) ?_).1 x
    calc
      |Real.smoothTransition s * a| = Real.smoothTransition s * |a| := by
        rw [abs_mul, abs_of_nonneg (Real.smoothTransition.nonneg s)]
      _ ≤ 1 * |a| := mul_le_mul_of_nonneg_right (Real.smoothTransition.le_one s) (abs_nonneg a)
      _ < δ := by simpa using haδ
  · intro ha'
    exact haA ⟨h p + a, ha', by ring⟩



theorem exists_supported_morse_zero_section_shift {n : Nat} (c : Real)
    (σ : Fin n -> Real) (hσ : ∀ i, σ i = -1 ∨ σ i = 1)
    {r R S ε : Real} (hr : 0 < r) (hrR : r < R) (hS : 0 < S) (hε : 0 < ε)
    {A : Set Real} (hA : A.Finite) :
    ∃ (b : EuclideanSpace Real (Fin n) -> Real) (a : Real)
        (F : Real -> Diffeomorph
          𝓘(Real, EuclideanSpace Real (Fin n) × Real)
          𝓘(Real, EuclideanSpace Real (Fin n) × Real)
          (EuclideanSpace Real (Fin n) × Real) (EuclideanSpace Real (Fin n) × Real) ∞),
      ContDiff Real ∞ b ∧ tsupport b ⊆ closedBall 0 R ∧
      EqOn b 1 (closedBall 0 r) ∧ |a| < ε ∧
      (∀ z, F 0 z = z) ∧
      ContDiff Real ∞
        (fun z : Real × (EuclideanSpace Real (Fin n) × Real) => F z.1 z.2) ∧
      (∀ s z, z ∉ closedBall 0 R ×ˢ closedBall (0 : Real) S -> F s z = z) ∧
      (∀ s x, F s (x, 0) = (x, Real.smoothTransition s * a * b x)) ∧
      (∀ s x, fderiv Real
        (fun y : EuclideanSpace Real (Fin n) =>
          c + (∑ i, σ i * y i ^ 2) + (Real.smoothTransition s * a) * b y) x = 0 ↔
          x = 0) ∧ c + a ∉ A := by
  let h : EuclideanSpace Real (Fin n) -> Real := fun x => c + ∑ i, σ i * x i ^ 2
  have hh : ContDiff Real ∞ h := Poincare.Analysis.Calculus.Morse.contDiff_diagonal_quadratic c σ
  have hσne (i : Fin n) : σ i ≠ 0 := by
    rcases hσ i with hi | hi <;> simp [hi]
  have hcrit (x : EuclideanSpace Real (Fin n)) : fderiv Real h x = 0 ↔ x = 0 :=
    Poincare.Analysis.Calculus.Morse.fderiv_diagonal_quadratic_eq_zero_iff c σ hσne x
  have hreg : ∀ x ∈ closedBall (0 : EuclideanSpace Real (Fin n)) R \ ball 0 r,
      fderiv Real h x ≠ 0 := by
    intro x hx hzero
    exact hx.2 ((hcrit x).mp hzero ▸ mem_ball_self hr)
  obtain ⟨b, a, F, hb, hbR, hbone, ha, hF0, hFs, hFfix, hFzero, hcritical, havoid⟩ :=
    exists_supported_zero_section_height_shift hh 0 hr hrR hS hε hreg hA
  refine ⟨b, a, F, hb, hbR, hbone, ha, hF0, hFs, hFfix, hFzero,
    fun s x => (hcritical s x).trans (hcrit x), ?_⟩
  simpa [h] using havoid

end Poincare.Manifold.Schoenflies
