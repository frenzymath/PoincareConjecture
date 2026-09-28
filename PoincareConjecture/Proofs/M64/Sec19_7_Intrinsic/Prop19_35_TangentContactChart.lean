import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_PolarInverse
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.Sard.OneDimensional












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff Bundle Matrix

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace






theorem m64Intrinsic_curve_tangent_chart_bases_null
    (e : AnnulusCoordinates → AnnulusCoordinates) (he : ContDiff ℝ ∞ e)
    (F : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (hF : (F : AnnulusCoordinates → AnnulusCoordinates) = e)
    (hFi : ContDiffOn ℝ ∞ F.symm F.target)
    {target : ℝ → AnnulusCoordinates} (htarget : ContDiff ℝ ∞ target) :
    volume {a : ℝ | ∃ t s : ℝ,
      !₂[a, t] ∈ F.source ∧ e !₂[a, t] = target s ∧
      Function.Injective (mfderiv (𝓡 2) (𝓡 2) e !₂[a, t]) ∧
      ¬ LinearIndependent ℝ
        (![deriv target s, fderiv ℝ e !₂[a, t] !₂[0, 1]] :
          Fin 2 → AnnulusCoordinates)} = 0 := by
  classical
  let J := target ⁻¹' F.target
  let q : ℝ → AnnulusCoordinates := F.symm ∘ target
  let f : ℝ → ℝ := fun s => q s 0
  have hJ : IsOpen J := F.open_target.preimage htarget.continuous
  have hq : ContDiffOn ℝ ∞ q J :=
    hFi.comp htarget.contDiffOn (fun _ hs => hs)
  have hdq (s : ℝ) (hs : s ∈ J) : DifferentiableAt ℝ q s :=
    (hq.contDiffAt (hJ.mem_nhds hs)).differentiableAt (by simp)
  have hdf (s : ℝ) (hs : s ∈ J) : HasDerivAt f (deriv q s 0) s :=
    (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (q s) 0).comp_hasDerivAt s
      (hdq s hs).hasDerivAt
  have hf : DifferentiableOn ℝ f J := fun s hs =>
    (hdf s hs).differentiableAt.differentiableWithinAt
  apply measure_mono_null ?_
    (Poincare.Analysis.critical_values_null_of_differentiableOn hJ hf)
  rintro a ⟨t, s, hsource, hpoint, hregular, htangent⟩
  have hs : s ∈ J := by
    change target s ∈ F.target
    rw [← hpoint, ← hF]
    exact F.map_source hsource
  have hqs : q s = !₂[a, t] := by
    change F.symm (target s) = !₂[a, t]
    rw [← hpoint, ← hF]
    exact F.left_inv hsource
  have hlift : (e ∘ q) =ᶠ[𝓝 s] target := by
    filter_upwards [hJ.mem_nhds hs] with z hz
    change e (F.symm (target z)) = target z
    rw [← hF]
    exact F.right_inv hz
  have hchain : HasDerivAt (e ∘ q)
      (fderiv ℝ e (q s) (deriv q s)) s :=
    (he.differentiable (by simp) (q s)).hasFDerivAt.comp_hasDerivAt s
      (hdq s hs).hasDerivAt
  have hd : fderiv ℝ e !₂[a, t] (deriv q s) = deriv target s := by
    rw [← hqs]
    exact (hchain.congr_of_eventuallyEq hlift.symm).deriv.symm
  have hinj : Function.Injective (fderiv ℝ e !₂[a, t]) := by
    simpa only [TangentSpace, mfderiv_eq_fderiv] using hregular
  have hvertical : (!₂[0, 1] : AnnulusCoordinates) ≠ 0 := by
    intro hz
    have h := congrArg (fun v : AnnulusCoordinates => v 1) hz
    norm_num at h
  have hnonzero : fderiv ℝ e !₂[a, t] !₂[0, 1] ≠ 0 := by
    intro hz
    apply hvertical
    apply hinj
    simpa only [map_zero] using hz
  rw [linearIndependent_fin2] at htangent
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at htangent
  have hscalar : ∃ c : ℝ,
      c • fderiv ℝ e !₂[a, t] !₂[0, 1] = deriv target s := by
    by_contra hn
    push Not at hn
    exact htangent ⟨hnonzero, hn⟩
  obtain ⟨c, hc⟩ := hscalar
  have hqvertical : deriv q s = c • (!₂[0, 1] : AnnulusCoordinates) := by
    apply hinj
    rw [map_smul, hd, hc]
  refine ⟨s, ⟨hs, ?_⟩, ?_⟩
  · rw [(hdf s hs).deriv, hqvertical]
    simp only [PiLp.smul_apply, Matrix.cons_val_zero, smul_zero]
  · change q s 0 = a
    rw [hqs]
    rfl

end PoincareConjecture
