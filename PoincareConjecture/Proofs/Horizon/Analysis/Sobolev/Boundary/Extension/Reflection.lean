import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.Boundary.TangentialTests
import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.Boundary.Extension.NormalCutoff
import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.Boundary.Extension.TestBound
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Filter
open scoped Topology ENNReal ContDiff

namespace Poincare.Analysis.Sobolev.BoundaryExtension

open Weak BoundaryTangential

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

def coordinateSign (i : Fin d) : ℝ := if i = 0 then -1 else 1


def reflect : E ≃ₗᵢ[ℝ] E where
  toFun x := WithLp.toLp 2 (fun i => coordinateSign i * x i)
  invFun x := WithLp.toLp 2 (fun i => coordinateSign i * x i)
  left_inv x := by
    ext i
    by_cases hi : i = 0 <;> simp [coordinateSign, hi]
  right_inv x := by
    ext i
    by_cases hi : i = 0 <;> simp [coordinateSign, hi]
  map_add' x y := by
    ext i
    simp [mul_add]
  map_smul' c x := by
    ext i
    simp [mul_left_comm]
  norm_map' x := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i = 0 <;> simp [coordinateSign, hi]

@[simp] theorem reflect_apply_zero (x : E) : reflect x 0 = -x 0 := by
  simp [reflect, coordinateSign]

@[simp] theorem reflect_apply_ne (x : E) (i : Fin d) (hi : i ≠ 0) : reflect x i = x i := by
  simp [reflect, coordinateSign, hi]

@[simp] theorem reflect_reflect (x : E) : reflect (reflect x) = x := reflect.left_inv x

theorem measurePreserving_reflect : MeasurePreserving (reflect (d := d)) volume volume :=
  reflect.measurePreserving

private theorem reflect_single (i : Fin d) :
    reflect (EuclideanSpace.single i 1) = coordinateSign i • EuclideanSpace.single i 1 := by
  ext j
  by_cases hj : j = i
  · subst j
    simp [reflect]
  · simp [reflect, hj]


def evenReflect (u : E → ℝ) (x : E) : ℝ :=
  (halfSpace d).indicator u x + (halfSpace d).indicator u (reflect x)


def reflectedPartial (i : Fin d) (g : E → ℝ) (x : E) : ℝ :=
  (halfSpace d).indicator g x + coordinateSign i * (halfSpace d).indicator g (reflect x)

theorem evenReflect_eq_on_halfSpace (u : E → ℝ) : EqOn (evenReflect u) u (halfSpace d) := by
  intro x hx
  have hRx : reflect x ∉ halfSpace d := by
    change ¬ 0 < reflect x 0
    rw [reflect_apply_zero]
    exact not_lt.mpr (neg_nonpos.mpr (le_of_lt hx))
  simp [evenReflect, hx, hRx]

theorem hasCompactSupport_evenReflect {u : E → ℝ} (hu : HasCompactSupport u) :
    HasCompactSupport (evenReflect u) := by
  have hi : HasCompactSupport ((halfSpace d).indicator u) := by
    apply hu.mono
    intro x hx
    by_cases h : x ∈ halfSpace d
    · simpa [h] using hx
    · simp [h] at hx
  exact hi.add (hi.comp_homeomorph reflect.toHomeomorph)

theorem memLp_evenReflect {p : ℝ≥0∞} {u : E → ℝ}
    (hu : MemLp u p (volume.restrict (halfSpace d))) :
    MemLp (evenReflect u) p volume := by
  have hi := (memLp_indicator_iff_restrict isOpen_halfSpace.measurableSet).mpr hu
  exact hi.add (hi.comp_measurePreserving measurePreserving_reflect)

theorem eLpNorm_evenReflect_le {p : ℝ≥0∞} (hp : 1 ≤ p) {u : E → ℝ}
    (hu : MemLp u p (volume.restrict (halfSpace d))) :
    eLpNorm (evenReflect u) p volume ≤
      2 * eLpNorm u p (volume.restrict (halfSpace d)) := by
  have hi := (memLp_indicator_iff_restrict isOpen_halfSpace.measurableSet).mpr hu
  calc
    _ ≤ eLpNorm ((halfSpace d).indicator u) p volume +
        eLpNorm ((halfSpace d).indicator u ∘ reflect) p volume :=
      eLpNorm_add_le hi.1 (hi.comp_measurePreserving measurePreserving_reflect).1 hp
    _ = _ := by
      rw [eLpNorm_comp_measurePreserving hi.1 measurePreserving_reflect,
        eLpNorm_indicator_eq_eLpNorm_restrict isOpen_halfSpace.measurableSet, two_mul]

private theorem memLp_reflectedPartial {p : ℝ≥0∞} {g : E → ℝ}
    (hg : MemLp g p (volume.restrict (halfSpace d))) (i : Fin d) :
    MemLp (reflectedPartial i g) p volume := by
  have hi := (memLp_indicator_iff_restrict isOpen_halfSpace.measurableSet).mpr hg
  exact hi.add ((hi.comp_measurePreserving measurePreserving_reflect).const_mul (coordinateSign i))

private theorem integral_indicator_mul (u q : E → ℝ) :
    (∫ x, (halfSpace d).indicator u x * q x) =
      ∫ x in halfSpace d, u x * q x := by
  rw [← integral_indicator isOpen_halfSpace.measurableSet]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    by_cases hx : x ∈ halfSpace d <;> simp [hx]

private theorem integral_reflection_pair {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u q : E → ℝ} (hu : MemLp u p (volume.restrict (halfSpace d)))
    (hq : Continuous q) (hc : HasCompactSupport q) (c : ℝ) :
    (∫ x, ((halfSpace d).indicator u x + c * (halfSpace d).indicator u (reflect x)) * q x) =
      ∫ x in halfSpace d, u x * (q x + c * q (reflect x)) := by
  have hi := (memLp_indicator_iff_restrict isOpen_halfSpace.measurableSet).mpr hu
  have hqR : Continuous (q ∘ reflect) := hq.comp reflect.continuous
  have hcR : HasCompactSupport (q ∘ reflect) := hc.comp_homeomorph reflect.toHomeomorph
  have hI : Integrable (fun x => (halfSpace d).indicator u x * q x) :=
    hi.locallyIntegrable hp |>.integrable_smul_right_of_hasCompactSupport hq hc
  have hIR : Integrable (fun x => (halfSpace d).indicator u x * q (reflect x)) :=
    hi.locallyIntegrable hp |>.integrable_smul_right_of_hasCompactSupport hqR hcR
  have hRI : Integrable (fun x => (halfSpace d).indicator u (reflect x) * q x) := by
    simpa only [Function.comp_def, reflect_reflect] using
      measurePreserving_reflect.integrable_comp_of_integrable hIR
  have hchange : (∫ x, (halfSpace d).indicator u (reflect x) * q x) =
      ∫ x in halfSpace d, u x * q (reflect x) := by
    rw [← integral_indicator_mul u (fun x => q (reflect x))]
    simpa only [Function.comp_def, reflect_reflect] using
      measurePreserving_reflect.integral_comp reflect.toHomeomorph.measurableEmbedding
        (fun x => (halfSpace d).indicator u x * q (reflect x))
  have hUH : Integrable (fun x => u x * q x) (volume.restrict (halfSpace d)) :=
    hu.locallyIntegrable hp |>.integrable_smul_right_of_hasCompactSupport hq hc
  have hUR : Integrable (fun x => u x * q (reflect x)) (volume.restrict (halfSpace d)) :=
    hu.locallyIntegrable hp |>.integrable_smul_right_of_hasCompactSupport hqR hcR
  calc
    _ = (∫ x, (halfSpace d).indicator u x * q x) +
        c * ∫ x, (halfSpace d).indicator u (reflect x) * q x := by
      rw [← integral_const_mul, ← integral_add hI (hRI.const_mul c)]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by ring
    _ = (∫ x in halfSpace d, u x * q x) + c * ∫ x in halfSpace d, u x * q (reflect x) := by
      rw [integral_indicator_mul, hchange]
    _ = _ := by
      rw [← integral_const_mul, ← integral_add hUH (hUR.const_mul c)]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by ring

private theorem reflected_test_partial {φ : E → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (i : Fin d) (x : E) :
    fderiv ℝ (fun y => φ y + coordinateSign i * φ (reflect y)) x
      (EuclideanSpace.single i 1) =
      fderiv ℝ φ x (EuclideanSpace.single i 1) +
        fderiv ℝ φ (reflect x) (EuclideanSpace.single i 1) := by
  have hd := ((hφ.differentiable (by simp) x).hasFDerivAt.add
    (((hφ.differentiable (by simp) (reflect x)).hasFDerivAt.comp x
      reflect.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt).const_mul
        (coordinateSign i))).fderiv
  have h := congrArg (fun L : E →L[ℝ] ℝ => L (EuclideanSpace.single i 1)) hd
  change fderiv ℝ (fun y => φ y + coordinateSign i * φ (reflect y)) x
      (EuclideanSpace.single i 1) =
    fderiv ℝ φ x (EuclideanSpace.single i 1) + coordinateSign i *
      fderiv ℝ φ (reflect x) (reflect (EuclideanSpace.single i 1)) at h
  rw [reflect_single, map_smul, smul_eq_mul] at h
  convert h using 1
  by_cases hi : i = 0 <;> simp [coordinateSign, hi]

private theorem reflected_test_zero_on_face (φ : E → ℝ) {x : E} (hx : x 0 = 0) :
    φ x + coordinateSign (0 : Fin d) * φ (reflect x) = 0 := by
  have hRx : reflect x = x := by
    ext i
    by_cases hi : i = 0
    · subst i
      simp [hx]
    · exact reflect_apply_ne x i hi
  simp [coordinateSign, hRx]

private theorem weakPartial_test_limit
    {p : ℝ≥0∞} (hp : 1 ≤ p) {u g ψ : E → ℝ} (i : Fin d)
    (hu : MemLp u p (volume.restrict (halfSpace d)))
    (hg : MemLp g p (volume.restrict (halfSpace d)))
    (hw : HasWeakPartialDeriv i g u (halfSpace d))
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (θ : ℕ → E → ℝ) (hs : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (θ n))
    (hθc : ∀ n, tsupport (θ n) ⊆ halfSpace d)
    (hnorm : ∀ n x, ‖θ n x‖ ≤ 1)
    (hlim : ∀ x ∈ halfSpace d, Tendsto (fun n => θ n x) atTop (𝓝 1))
    (herr : Tendsto (fun n => ∫ x in halfSpace d,
      u x * ψ x * fderiv ℝ (θ n) x (EuclideanSpace.single i 1)) atTop (𝓝 0)) :
    (∫ x in halfSpace d, u x * fderiv ℝ ψ x (EuclideanSpace.single i 1)) =
      -(∫ x in halfSpace d, g x * ψ x) := by
  let dψ : E → ℝ := fun x => fderiv ℝ ψ x (EuclideanSpace.single i 1)
  have hdc : Continuous dψ := (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hds : HasCompactSupport dψ := hc.fderiv_apply (𝕜 := ℝ) _
  have hdint : Integrable (fun x => u x * dψ x) (volume.restrict (halfSpace d)) :=
    hu.locallyIntegrable hp |>.integrable_smul_right_of_hasCompactSupport hdc hds
  have hgint : Integrable (fun x => g x * ψ x) (volume.restrict (halfSpace d)) :=
    hg.locallyIntegrable hp |>.integrable_smul_right_of_hasCompactSupport hψ.continuous hc
  have hlimit {a : E → ℝ} (ha : Integrable a (volume.restrict (halfSpace d))) :
      Tendsto (fun n => ∫ x in halfSpace d, θ n x * a x) atTop
        (𝓝 (∫ x in halfSpace d, a x)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => ‖a x‖)
    · intro n
      exact ((hs n).continuous.aestronglyMeasurable.restrict).mul ha.aestronglyMeasurable
    · exact ha.norm
    · intro n
      exact Eventually.of_forall fun x => by
        rw [norm_mul]
        exact (mul_le_mul_of_nonneg_right (hnorm n x) (norm_nonneg _)).trans_eq (one_mul _)
    · filter_upwards [ae_restrict_mem isOpen_halfSpace.measurableSet] with x hx
      simpa using (hlim x hx).mul_const (a x)
  have heq (n : ℕ) :
      (∫ x in halfSpace d, θ n x * (u x * dψ x)) +
        (∫ x in halfSpace d, u x * ψ x * fderiv ℝ (θ n) x (EuclideanSpace.single i 1)) =
      -(∫ x in halfSpace d, θ n x * (g x * ψ x)) := by
    have ha : Integrable (fun x => θ n x * (u x * dψ x))
        (volume.restrict (halfSpace d)) := by
      convert hu.locallyIntegrable hp |>.integrable_smul_right_of_hasCompactSupport
        ((hs n).continuous.mul hdc) hds.mul_left using 1
      ext x
      simp only [smul_eq_mul, Pi.mul_apply]
      ring
    have hb : Integrable
        (fun x => u x * ψ x * fderiv ℝ (θ n) x (EuclideanSpace.single i 1))
        (volume.restrict (halfSpace d)) := by
      convert hu.locallyIntegrable hp |>.integrable_smul_right_of_hasCompactSupport
        (hψ.continuous.mul ((hs n).continuous_fderiv (by simp) |>.clm_apply
          (continuous_const (y := EuclideanSpace.single i 1))))
        hc.mul_right using 1
      ext x
      simp only [smul_eq_mul, Pi.mul_apply]
      ring
    rw [← integral_add ha hb]
    have hprod (x : E) :
        fderiv ℝ (fun y => θ n y * ψ y) x (EuclideanSpace.single i 1) =
          θ n x * dψ x + ψ x * fderiv ℝ (θ n) x (EuclideanSpace.single i 1) := by
      have hd := (((hs n).differentiable (by simp) x).hasFDerivAt.mul
        (hψ.differentiable (by simp) x).hasFDerivAt).fderiv
      have h := congrArg (fun L : E →L[ℝ] ℝ => L (EuclideanSpace.single i 1)) hd
      simpa [dψ, Pi.mul_def] using h
    calc
      _ = ∫ x in halfSpace d, u x * fderiv ℝ (fun y => θ n y * ψ y) x
          (EuclideanSpace.single i 1) := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by dsimp only; rw [hprod]; ring
      _ = _ := hw _ ((hs n).mul hψ) hc.mul_left (tsupport_mul_subset_left.trans (hθc n))
      _ = _ := by
        congr 1
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by ring
  have hh := (hlimit hdint).add herr
  simpa only [add_zero] using tendsto_nhds_unique hh
    ((hlimit hgint).neg.congr' (Eventually.of_forall fun n => (heq n).symm))

private theorem normalCutoff_error_tendsto {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u ψ : E → ℝ} (hu : MemLp u p (volume.restrict (halfSpace d)))
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (hface : ∀ x : E, x 0 = 0 → ψ x = 0) :
    Tendsto (fun n => ∫ x in halfSpace d,
      u x * ψ x * fderiv ℝ (normalCutoff n) x (EuclideanSpace.single 0 1)) atTop (𝓝 0) := by
  obtain ⟨C, hC, hψbound⟩ := exists_norm_le_normalCoord hψ hc hface
  obtain ⟨D, hD, hθbound⟩ := exists_normalCutoff_normal_bound (d := d)
  have hI : Integrable ((tsupport ψ).indicator (fun x => ‖u x‖))
      (volume.restrict (halfSpace d)) :=
    (integrable_indicator_iff (isClosed_tsupport ψ).measurableSet).mpr
      ((hu.locallyIntegrable hp).integrableOn_isCompact hc).norm
  have h := tendsto_integral_of_dominated_convergence
    (fun x => C * D * (tsupport ψ).indicator (fun y => ‖u y‖) x)
    (μ := volume.restrict (halfSpace d))
    (F := fun n x => u x * ψ x *
      fderiv ℝ (normalCutoff n) x (EuclideanSpace.single 0 1))
    (f := fun _ => (0 : ℝ)) ?_ (hI.const_mul (C * D)) ?_ ?_
  · simpa using h
  · intro n
    exact (hu.1.mul hψ.continuous.aestronglyMeasurable.restrict).mul
      (((normalCutoff_smooth n).continuous_fderiv (by simp)).clm_apply
        continuous_const).aestronglyMeasurable.restrict
  · intro n
    filter_upwards [ae_restrict_mem isOpen_halfSpace.measurableSet] with x hx
    by_cases hs : x ∈ tsupport ψ
    · rw [indicator_of_mem hs, norm_mul, norm_mul]
      have hxb : ‖ψ x‖ * ‖fderiv ℝ (normalCutoff n) x (EuclideanSpace.single 0 1)‖ ≤ C * D := by
        calc
          _ ≤ (C * x 0) * ‖fderiv ℝ (normalCutoff n) x (EuclideanSpace.single 0 1)‖ :=
            mul_le_mul_of_nonneg_right (hψbound x hx.le) (norm_nonneg _)
          _ = C * (x 0 * ‖fderiv ℝ (normalCutoff n) x (EuclideanSpace.single 0 1)‖) := by ring
          _ ≤ C * D := mul_le_mul_of_nonneg_left (hθbound n x hx.le) hC
      nlinarith [norm_nonneg (u x)]
    · simp [indicator_of_notMem hs, image_eq_zero_of_notMem_tsupport hs]
  · filter_upwards [ae_restrict_mem isOpen_halfSpace.measurableSet] with x hx
    apply tendsto_const_nhds.congr'
    filter_upwards [normalCutoff_fderiv_eventually_eq_zero hx] with n hn
    simp [hn]

private theorem weakPartial_test_upToBoundary
    {p : ℝ≥0∞} (hp : 1 ≤ p) {u g ψ : E → ℝ} (i : Fin d)
    (hu : MemLp u p (volume.restrict (halfSpace d)))
    (hg : MemLp g p (volume.restrict (halfSpace d)))
    (hw : HasWeakPartialDeriv i g u (halfSpace d))
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (hface : i = 0 → ∀ x : E, x 0 = 0 → ψ x = 0) :
    (∫ x in halfSpace d, u x * fderiv ℝ ψ x (EuclideanSpace.single i 1)) =
      -(∫ x in halfSpace d, g x * ψ x) := by
  apply weakPartial_test_limit hp i hu hg hw hψ hc normalCutoff normalCutoff_smooth
    normalCutoff_tsupport normalCutoff_norm_le (fun _ hx => normalCutoff_tendsto hx)
  by_cases hi : i = 0
  · subst i
    exact normalCutoff_error_tendsto hp hu hψ hc (hface rfl)
  · simp [normalCutoff_partial _ _ hi]

theorem hasWeakPartialDeriv_evenReflect {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u g : E → ℝ} (i : Fin d)
    (hu : MemLp u p (volume.restrict (halfSpace d)))
    (hg : MemLp g p (volume.restrict (halfSpace d)))
    (hw : HasWeakPartialDeriv i g u (halfSpace d)) :
    HasWeakPartialDeriv i (reflectedPartial i g) (evenReflect u) Set.univ := by
  intro φ hφ hc _
  let ψ : E → ℝ := fun x => φ x + coordinateSign i * φ (reflect x)
  have hs : ContDiff ℝ (⊤ : ℕ∞) ψ :=
    hφ.add (contDiff_const.mul (hφ.comp reflect.toContinuousLinearEquiv.contDiff))
  have hcs : HasCompactSupport ψ :=
    hc.add (hc.comp_homeomorph reflect.toHomeomorph).mul_left
  have hface : i = 0 → ∀ x : E, x 0 = 0 → ψ x = 0 := by
    intro hi x hx
    subst i
    exact reflected_test_zero_on_face φ hx
  have ht := weakPartial_test_upToBoundary hp i hu hg hw hs hcs hface
  simp only [Measure.restrict_univ]
  have hleft := integral_reflection_pair hp hu
    ((hφ.continuous_fderiv (by simp)).clm_apply
      (continuous_const (y := EuclideanSpace.single i 1)))
    (hc.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)) 1
  have hright := integral_reflection_pair hp hg hφ.continuous hc (coordinateSign i)
  simp only [one_mul] at hleft
  change (∫ x, ((halfSpace d).indicator u x + (halfSpace d).indicator u (reflect x)) *
    fderiv ℝ φ x (EuclideanSpace.single i 1)) = _
  simp only [reflectedPartial]
  rw [hleft, hright]
  convert ht using 1
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    dsimp only [ψ]
    rw [reflected_test_partial hφ]


noncomputable def evenReflectMemW1pWitness {p : ℝ≥0∞} (hp : 1 ≤ p) (_hp_top : p ≠ ⊤)
    {u : E → ℝ} (hw : MemW1pWitness p u (halfSpace d)) :
    MemW1pWitness p (evenReflect u) Set.univ where
  memLp := by simpa using memLp_evenReflect hw.memLp
  weakGrad x := WithLp.toLp 2 (fun i => reflectedPartial i (fun y => hw.weakGrad y i) x)
  weakGrad_component_memLp i := by
    simpa using memLp_reflectedPartial (hw.weakGrad_component_memLp i) i
  isWeakGrad i := hasWeakPartialDeriv_evenReflect hp i hw.memLp
    (hw.weakGrad_component_memLp i) (hw.isWeakGrad i)

theorem evenReflectMemW1pWitness_weakGrad {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ⊤)
    {u : E → ℝ} (hw : MemW1pWitness p u (halfSpace d)) (i : Fin d) (x : E) :
    (evenReflectMemW1pWitness hp hp_top hw).weakGrad x i =
      reflectedPartial i (fun y => hw.weakGrad y i) x := rfl



theorem memW1p_evenReflect {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ⊤)
    {u : E → ℝ} (hu : MemW1p p u (halfSpace d)) :
    MemW1p p (evenReflect u) Set.univ :=
  (evenReflectMemW1pWitness hp hp_top hu.someWitness).memW1p

end Poincare.Analysis.Sobolev.BoundaryExtension
