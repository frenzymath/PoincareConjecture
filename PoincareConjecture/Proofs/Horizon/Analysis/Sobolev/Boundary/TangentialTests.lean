import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.EnergyEstimate.TestFunction.Standard
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Sobolev.Weak.Witnesses

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Filter
open scoped Topology ENNReal

namespace Poincare.Analysis.Sobolev.BoundaryTangential

open Weak NirenbergStandardTest

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

def halfSpace (d : ℕ) [NeZero d] : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | 0 < x 0}

theorem isOpen_halfSpace : IsOpen (halfSpace d) :=
  isOpen_lt continuous_const (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) 0)

theorem measurePreserving_translate_halfSpace (k : Fin d) (hk : k ≠ 0) (h : ℝ) :
    MeasurePreserving (fun x : E => x + h • EuclideanSpace.single k 1)
      (volume.restrict (halfSpace d)) (volume.restrict (halfSpace d)) := by
  have hpre : (fun x : E => x + h • EuclideanSpace.single k 1) ⁻¹' halfSpace d =
      halfSpace d := by
    ext x
    simp [halfSpace, PiLp.add_apply, PiLp.smul_apply, hk.symm]
  have hm := (measurePreserving_add_right (volume : Measure E)
    (h • EuclideanSpace.single k 1)).restrict_preimage isOpen_halfSpace.measurableSet
  rw [hpre] at hm
  exact hm

omit [NeZero d] in
private theorem fderiv_translate {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (k : Fin d) (h : ℝ) (x : E) :
    fderiv ℝ (translate k h u) x = fderiv ℝ u (x + h • EuclideanSpace.single k 1) := by
  have ht := (hasFDerivAt_id (𝕜 := ℝ) x).add_const (h • EuclideanSpace.single k (1 : ℝ))
  have hf := ((hu.differentiable (by simp) _).hasFDerivAt.comp x ht).fderiv
  simp only [ContinuousLinearMap.comp_id, Function.comp_def, id_eq] at hf
  convert! hf using 1

omit [NeZero d] in
private theorem memW01p_of_approximation {O : Set E} (hO : IsOpen O)
    {u : E → ℝ} {g : Fin d → E → ℝ}
    (hu : MemLp u 2 (volume.restrict O))
    (hg : ∀ i, MemLp (g i) 2 (volume.restrict O))
    (φ : ℕ → E → ℝ) (hφ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (φ j))
    (hc : ∀ j, HasCompactSupport (φ j)) (hs : ∀ j, tsupport (φ j) ⊆ O)
    (hv : Tendsto (fun j => eLpNorm (fun x => φ j x - u x) 2 (volume.restrict O))
      atTop (𝓝 0))
    (hd : ∀ i, Tendsto (fun j => eLpNorm
      (fun x => fderiv ℝ (φ j) x (EuclideanSpace.single i 1) - g i x)
        2 (volume.restrict O)) atTop (𝓝 0)) : MemW01p 2 u O := by
  have hw (i : Fin d) : HasWeakPartialDeriv i (g i) u O := by
    apply HasWeakPartialDeriv.of_eLpNormApprox_p hO (p := 2) (by norm_num)
      (by simpa using hu) (by simpa using hg i)
      (ψ := φ) (gψ := fun j x => fderiv ℝ (φ j) x (EuclideanSpace.single i 1))
    · intro j
      exact HasWeakPartialDeriv.of_contDiff hO ((hφ j).of_le (by norm_cast))
    · intro j
      convert! (((hφ j).continuous.memLp_of_hasCompactSupport (hc j)).restrict O).sub hu using 1
      norm_num
    · simpa using hv
    · intro j
      have hc' := (hc j).fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i (1 : ℝ))
      have hd' : Continuous (fun x => fderiv ℝ (φ j) x (EuclideanSpace.single i 1)) :=
        ((hφ j).continuous_fderiv (by simp)).clm_apply continuous_const
      convert! ((hd'.memLp_of_hasCompactSupport hc').restrict O).sub (hg i) using 1
      norm_num
    · simpa using hd i
  let w : MemW1pWitness 2 u O :=
    { memLp := hu
      weakGrad := fun x => WithLp.toLp 2 (fun i => g i x)
      weakGrad_component_memLp := hg
      isWeakGrad := hw }
  exact ⟨w.memW1p, w, φ, hφ, hc, hs, hv, hd⟩

theorem memW01p_translate {u : E → ℝ} (hu : MemW01p 2 u (halfSpace d))
    (k : Fin d) (hk : k ≠ 0) (h : ℝ) :
    MemW01p 2 (translate k h u) (halfSpace d) := by
  rcases hu with ⟨_, w, φ, hφ, hc, hs, hv, hd⟩
  let τ : E ≃ₜ E := Homeomorph.addRight (h • EuclideanSpace.single k 1)
  have hmp := measurePreserving_translate_halfSpace k hk h
  have hm (j : ℕ) : MemLp (φ j) 2 (volume.restrict (halfSpace d)) :=
    ((hφ j).continuous.memLp_of_hasCompactSupport (hc j)).restrict _
  apply memW01p_of_approximation isOpen_halfSpace
    (w.memLp.comp_measurePreserving hmp)
    (fun i => (w.weakGrad_component_memLp i).comp_measurePreserving hmp)
    (fun j => translate k h (φ j))
  · intro j
    exact (hφ j).comp (contDiff_id.add contDiff_const)
  · intro j
    exact (hc j).comp_homeomorph τ
  · intro j x hx
    have hxin : τ x ∈ tsupport (φ j) :=
      (tsupport_comp_subset_preimage (φ j) τ.continuous) hx
    have hpos := hs j hxin
    simpa [halfSpace, τ, PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, hk, hk.symm] using hpos
  · have heq (j : ℕ) :
        eLpNorm (fun x => translate k h (φ j) x - translate k h u x) 2
          (volume.restrict (halfSpace d)) =
        eLpNorm (fun x => φ j x - u x) 2 (volume.restrict (halfSpace d)) := by
      have ha : AEStronglyMeasurable (fun x => φ j x - u x)
          (volume.restrict (halfSpace d)) := by
        convert! ((hm j).sub w.memLp).aestronglyMeasurable using 1
      simpa only [translate, Function.comp_def] using
        eLpNorm_comp_measurePreserving (p := 2) ha hmp
    convert! hv using 1
    exact funext heq
  · intro i
    have heq (j : ℕ) : eLpNorm
        (fun x => fderiv ℝ (translate k h (φ j)) x (EuclideanSpace.single i 1) -
          w.weakGrad (x + h • EuclideanSpace.single k 1) i) 2
          (volume.restrict (halfSpace d)) =
        eLpNorm (fun x => fderiv ℝ (φ j) x (EuclideanSpace.single i 1) - w.weakGrad x i)
          2 (volume.restrict (halfSpace d)) := by
      simp only [fderiv_translate (hφ j)]
      have ha : AEStronglyMeasurable
          (fun x => fderiv ℝ (φ j) x (EuclideanSpace.single i 1) - w.weakGrad x i)
          (volume.restrict (halfSpace d)) :=
        ((((hφ j).continuous_fderiv (by simp)).clm_apply continuous_const).aestronglyMeasurable).sub
          (w.weakGrad_component_memLp i).aestronglyMeasurable
      simpa only [Function.comp_def] using eLpNorm_comp_measurePreserving (p := 2) ha hmp
    convert! hd i using 1
    exact funext heq

theorem memW01p_diffQuot {u : E → ℝ} (hu : MemW01p 2 u (halfSpace d))
    (k : Fin d) (hk : k ≠ 0) (h : ℝ) :
    MemW01p 2 (diffQuot k h u) (halfSpace d) := by
  have hm := ((memW01p_translate hu k hk h).sub hu).smul h⁻¹
  by_cases hh : h = 0
  · convert! hm using 1
    funext x
    simp [hh, diffQuot]
  · convert hm using 1
    funext x
    rw [diffQuot_apply_of_ne k hh]
    simp only [translate]
    ring

omit [NeZero d] in
private theorem exists_uniform_norm_bound {F : Type*} [NormedAddCommGroup F]
    {a : E → F} (ha : Continuous a) (hc : HasCompactSupport a) :
    ∃ C ≥ 0, ∀ x, ‖a x‖ ≤ C := by
  obtain ⟨C, hC⟩ := ha.norm.bddAbove_range_of_hasCompactSupport hc.norm
  exact ⟨max C 0, le_max_right _ _, fun x => (hC ⟨x, rfl⟩).trans (le_max_left _ _)⟩

private theorem tendsto_eLpNorm_bounded_mul {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {a : X → ℝ} {C : ℝ} (hC : ∀ x, ‖a x‖ ≤ C)
    {v : ℕ → X → ℝ} (hv : Tendsto (fun j => eLpNorm (v j) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun j => eLpNorm (fun x => a x * v j x) 2 μ) atTop (𝓝 0) := by
  have hb (j : ℕ) : eLpNorm (fun x => a x * v j x) 2 μ ≤
      ENNReal.ofReal C * eLpNorm (v j) 2 μ := by
    apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul _ 2
    exact Filter.Eventually.of_forall fun x => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds _
    (fun _ => bot_le) hb
  simpa using ENNReal.Tendsto.const_mul hv (Or.inr ENNReal.ofReal_ne_top)

omit [NeZero d] in

theorem memW01p_mul_smooth {O : Set E} (hO : IsOpen O) {u η : E → ℝ}
    (hu : MemW01p 2 u O) (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hc : HasCompactSupport η) :
    MemW01p 2 (fun x => η x * u x) O := by
  rcases hu with ⟨_, w, φ, hφ, hφc, hφs, hv, hd⟩
  obtain ⟨C₀, hC₀, hCη⟩ := exists_uniform_norm_bound hη.continuous hc
  obtain ⟨C₁, hC₁, hCDη⟩ := exists_uniform_norm_bound
    (hη.continuous_fderiv (by simp)) (hc.fderiv ℝ)
  let w' := w.mulSmoothBoundedP (by norm_num : (1 : ℝ≥0∞) ≤ 2) hO hη hC₀ hC₁
    (by simpa only [Real.norm_eq_abs] using hCη) hCDη
  refine ⟨w'.memW1p, w', fun j x => η x * φ j x, fun j => hη.mul (hφ j),
    fun j => (hφc j).mul_left, fun j => (tsupport_mul_subset_right).trans (hφs j), ?_, ?_⟩
  · have hlim := tendsto_eLpNorm_bounded_mul hCη hv
    convert hlim using 1
    ext j
    congr 1
    funext x
    ring
  · intro i
    let a : E → ℝ := fun x => fderiv ℝ η x (EuclideanSpace.single i 1)
    have hCa (x : E) : ‖a x‖ ≤ C₁ := by
      have hop : ‖a x‖ ≤ ‖fderiv ℝ η x‖ := by
        simpa [a] using (fderiv ℝ η x).le_opNorm (EuclideanSpace.single i (1 : ℝ))
      exact hop.trans (hCDη x)
    have ha : Continuous a := (hη.continuous_fderiv (by simp)).clm_apply continuous_const
    have hlim₁ := tendsto_eLpNorm_bounded_mul hCη (hd i)
    have hlim₀ := tendsto_eLpNorm_bounded_mul hCa hv
    have hb (j : ℕ) : eLpNorm
        (fun x => fderiv ℝ (fun y => η y * φ j y) x (EuclideanSpace.single i 1) -
          w'.weakGrad x i) 2 (volume.restrict O) ≤
        eLpNorm (fun x => η x *
          (fderiv ℝ (φ j) x (EuclideanSpace.single i 1) - w.weakGrad x i)) 2 (volume.restrict O) +
        eLpNorm (fun x => a x * (φ j x - u x)) 2 (volume.restrict O) := by
      have heq : (fun x => fderiv ℝ (fun y => η y * φ j y) x (EuclideanSpace.single i 1) -
          w'.weakGrad x i) = fun x =>
          η x * (fderiv ℝ (φ j) x (EuclideanSpace.single i 1) - w.weakGrad x i) +
            a x * (φ j x - u x) := by
        funext x
        have hmul : fderiv ℝ (fun y => η y * φ j y) x =
            η x • fderiv ℝ (φ j) x + φ j x • fderiv ℝ η x := by
          convert! fderiv_mul (hη.differentiable (by simp) x)
            ((hφ j).differentiable (by simp) x) using 1
        rw [hmul]
        simp [w', MemW1pWitness.mulSmoothBoundedP, a]
        ring
      rw [heq]
      apply eLpNorm_add_le _ _ (by norm_num)
      · exact hη.continuous.aestronglyMeasurable.mul
          ((((hφ j).continuous_fderiv (by simp)).clm_apply continuous_const).aestronglyMeasurable.sub
            (w.weakGrad_component_memLp i).aestronglyMeasurable)
      · exact ha.aestronglyMeasurable.mul
          ((hφ j).continuous.aestronglyMeasurable.sub w.memLp.aestronglyMeasurable)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds _
      (fun _ => bot_le) hb
    simpa using hlim₁.add hlim₀

theorem memW01p_standardNirenbergTest {u η : E → ℝ}
    (hu : MemW01p 2 u (halfSpace d))
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hc : HasCompactSupport η)
    (k : Fin d) (hk : k ≠ 0) (h : ℝ) :
    MemW01p 2 (standardNirenbergTest k h η u) (halfSpace d) := by
  apply memW01p_diffQuot (k := k) (hk := hk) (h := -h)
  apply memW01p_mul_smooth isOpen_halfSpace (memW01p_diffQuot hu k hk h) (hη.pow 2)
  simpa only [pow_two, Pi.mul_def] using hc.mul_right (f' := η)

end Poincare.Analysis.Sobolev.BoundaryTangential
