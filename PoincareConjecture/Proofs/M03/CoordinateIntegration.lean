import PoincareConjecture.Definitions.Ch01.RiemannianMetric
import Mathlib.Analysis.Calculus.ParametricIntegral










set_option autoImplicit false

open scoped ContDiff Topology
open MeasureTheory Set

namespace PoincareConjecture.Proofs.M03

theorem integral_fderiv_eq_zero_of_hasCompactSupport
    {n : ℕ} {P : EuclideanSpace ℝ (Fin n) → ℝ}
    (hP : ContDiff ℝ 1 P) (hPc : HasCompactSupport P)
    (v : EuclideanSpace ℝ (Fin n)) :
    letI : MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _
    letI : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
    (∫ x, fderiv ℝ P x v) = 0 := by
  let : MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _
  let : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
  classical
  let H : ℝ → EuclideanSpace ℝ (Fin n) → ℝ := fun s x => P (x + s • v)
  let D : ℝ → EuclideanSpace ℝ (Fin n) → ℝ :=
    fun s x => fderiv ℝ P (x + s • v) v
  let K : Set (EuclideanSpace ℝ (Fin n)) :=
    (fun p : ℝ × EuclideanSpace ℝ (Fin n) => p.2 - p.1 • v) ''
      (Icc (-1 : ℝ) 1 ×ˢ tsupport P)
  have hK : IsCompact K :=
    (isCompact_Icc.prod hPc).image (continuous_snd.sub (continuous_fst.smul continuous_const))
  have hH : Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin n) => H p.1 p.2) :=
    hP.continuous.comp (continuous_snd.add (continuous_fst.smul continuous_const))
  have hD : Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin n) => D p.1 p.2) :=
    ((hP.continuous_fderiv (by decide)).comp
      (continuous_snd.add (continuous_fst.smul continuous_const))).clm_apply continuous_const
  have hDzero : ∀ s ∈ Icc (-1 : ℝ) 1, ∀ x ∉ K, D s x = 0 := by
    intro s hs x hx
    have hp : x + s • v ∉ tsupport P := by
      intro hp
      apply hx
      exact ⟨(s, x + s • v), ⟨hs, hp⟩, by simp⟩
    change fderiv ℝ P (x + s • v) v = 0
    rw [fderiv_of_notMem_tsupport ℝ hp]
    rfl
  have hrect := (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1)).prod hK
  obtain ⟨C, hC⟩ := hrect.exists_bound_of_continuousOn hD.continuousOn
  have hbound : Integrable (K.indicator (fun _ => max C 0)) :=
    (integrableOn_const (C := max C 0) hK.measure_ne_top).integrable_indicator hK.isClosed.measurableSet
  have hdiff : ∀ s x, HasDerivAt (fun r => H r x) (D s x) s := by
    intro s x
    simpa [H, D] using! ((hP.differentiable (by decide) (x + s • v)).hasFDerivAt.comp_hasDerivAt s
      (HasDerivAt.const_add x ((hasDerivAt_id s).smul_const v)))
  have hint : HasDerivAt (fun s : ℝ => ∫ x, H s x) (∫ x, D 0 x) 0 := by
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := H) (F' := D) (bound := K.indicator (fun _ => max C 0))
      (Icc_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1))
      ?_ ?_ ?_ ?_ hbound ?_).2
    · exact Filter.Eventually.of_forall fun s =>
        (hH.comp (.prodMk_right s)).aestronglyMeasurable
    · simpa [H] using hP.continuous.integrable_of_hasCompactSupport hPc
    · exact (hD.comp (.prodMk_right 0)).aestronglyMeasurable
    · filter_upwards with x
      intro s hs
      by_cases hx : x ∈ K
      · rw [indicator_of_mem hx]
        exact (hC (s, x) ⟨hs, hx⟩).trans (le_max_left _ _)
      · simp [indicator_of_notMem hx, hDzero s hs x hx]
    · filter_upwards with x
      intro s _
      exact hdiff s x
  have heq : (fun s : ℝ => ∫ x, H s x) = fun _ => ∫ x, P x := by
    funext s
    exact integral_add_right_eq_self P (s • v)
  rw [heq] at hint
  simpa [D] using hint.unique (hasDerivAt_const (0 : ℝ) (∫ x, P x))

theorem integral_localized_mul_fderiv
    {n : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f g φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiffOn ℝ 1 f U) (hg : ContDiffOn ℝ 1 g U)
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) (v : EuclideanSpace ℝ (Fin n)) :
    letI : MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _
    letI : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
    (∫ x, φ x ^ 2 * f x * fderiv ℝ g x v) =
      -(∫ x, (φ x ^ 2 * fderiv ℝ f x v +
        2 * φ x * fderiv ℝ φ x v * f x) * g x) := by
  let : MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _
  let : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
  classical
  let P : EuclideanSpace ℝ (Fin n) → ℝ := fun x => φ x ^ 2 * f x * g x
  let A : EuclideanSpace ℝ (Fin n) → ℝ := fun x => φ x ^ 2 * f x * fderiv ℝ g x v
  let B : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun x => (φ x ^ 2 * fderiv ℝ f x v + 2 * φ x * fderiv ℝ φ x v * f x) * g x
  have hP : ContDiff ℝ 1 P := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ U
    · exact (((hφ.contDiffAt.pow 2).mul (hf.contDiffAt (hU.mem_nhds hx))).mul
        (hg.contDiffAt (hU.mem_nhds hx)))
    · have hxφ : x ∉ tsupport φ := fun h => hx (hφU h)
      apply (show ContDiffAt ℝ 1 (fun _ : EuclideanSpace ℝ (Fin n) => (0 : ℝ)) x from
        contDiffAt_const).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hxφ] with y hy
      simp [P, hy]
  have hPc : HasCompactSupport P :=
    ((hφc.comp_left (g := fun y : ℝ => y ^ 2) (by simp)).mul_right (f' := f)).mul_right (f' := g)
  have hpatch : ∀ Q : EuclideanSpace ℝ (Fin n) → ℝ, ContinuousOn Q U →
      (∀ x ∉ tsupport φ, Q x = 0) → Continuous Q ∧ HasCompactSupport Q := by
    intro Q hQ hzero
    constructor
    · apply continuous_iff_continuousAt.mpr
      intro x
      by_cases hx : x ∈ U
      · exact hQ.continuousAt (hU.mem_nhds hx)
      · have hxφ : x ∈ (tsupport φ)ᶜ := fun h => hx (hφU h)
        apply continuousAt_const.congr_of_eventuallyEq
        filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hxφ] with y hy
        exact hzero y hy
    · apply hφc.mono'
      intro x hx
      by_contra hxφ
      exact hx (hzero x hxφ)
  have hA : Continuous A ∧ HasCompactSupport A := hpatch A
    (((hφ.continuous.continuousOn.pow 2).mul hf.continuousOn).mul
      ((hg.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const))
    (fun x hx => by simp [A, image_eq_zero_of_notMem_tsupport hx])
  have hB : Continuous B ∧ HasCompactSupport B := hpatch B
    ((((hφ.continuous.continuousOn.pow 2).mul
      ((hf.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const)).add
      (((continuousOn_const.mul hφ.continuous.continuousOn).mul
        (((hφ.continuous_fderiv (by decide)).clm_apply continuous_const).continuousOn)).mul
          hf.continuousOn)).mul hg.continuousOn)
    (fun x hx => by simp [B, image_eq_zero_of_notMem_tsupport hx])
  have hformula : ∀ x, fderiv ℝ P x v = A x + B x := by
    intro x
    by_cases hx : x ∈ U
    · have hf' := ((hf.contDiffAt (hU.mem_nhds hx)).differentiableAt (by decide)).hasFDerivAt
      have hg' := ((hg.contDiffAt (hU.mem_nhds hx)).differentiableAt (by decide)).hasFDerivAt
      have hφ' := (hφ.differentiable (by decide) x).hasFDerivAt
      have hprod := ((hφ'.pow 2).mul hf').mul hg'
      have heq : fderiv ℝ P x v =
          (φ x ^ 2 * f x) * fderiv ℝ g x v +
            g x * (φ x ^ 2 * fderiv ℝ f x v + f x * ((2 * φ x) * fderiv ℝ φ x v)) := by
        simpa only [P, Pi.mul_apply, add_apply, smul_apply,
          Nat.reduceSub, pow_one, nsmul_eq_mul, Nat.cast_ofNat, smul_eq_mul] using!
          congrArg (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => L v) hprod.fderiv
      rw [heq]
      dsimp only [A, B]
      ring
    · have hxφ : x ∉ tsupport φ := fun h => hx (hφU h)
      have hPzero : P =ᶠ[𝓝 x] 0 := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hxφ] with y hy
        simp [P, hy]
      simp [fderiv_of_notMem_tsupport ℝ (notMem_tsupport_iff_eventuallyEq.mpr hPzero),
        A, B, image_eq_zero_of_notMem_tsupport hxφ]
  have hzero := integral_fderiv_eq_zero_of_hasCompactSupport hP hPc v
  change (∫ x, fderiv ℝ P x v) = 0 at hzero
  simp_rw [hformula] at hzero
  rw [integral_add (hA.1.integrable_of_hasCompactSupport hA.2)
    (hB.1.integrable_of_hasCompactSupport hB.2)] at hzero
  change (∫ x, A x) = -(∫ x, B x)
  linarith

end PoincareConjecture.Proofs.M03
