import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_MeasurableNormalStrip
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_PolarInverse













noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle Matrix

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace




theorem m64Intrinsic_boundary_lift_speed_le
    (N : IntrinsicAnnulus)
    {e : AnnulusCoordinates → AnnulusCoordinates} {gamma : ℝ → AnnulusCoordinates}
    {s c : ℝ} (he : DifferentiableAt ℝ e (gamma s)) (hg : DifferentiableAt ℝ gamma s)
    (hlift : (e ∘ gamma) =ᶠ[𝓝 s] intrinsicAnnulusBoundary 2)
    (hbound : ∀ v : AnnulusCoordinates,
      c ^ 2 * ((intrinsicBoundarySpeed N.metric 1 (gamma s 0)) ^ 2 * (v 0) ^ 2 + (v 1) ^ 2) ≤
        N.metric.inner (e (gamma s)) (fderiv ℝ e (gamma s) v) (fderiv ℝ e (gamma s) v)) :
    c * intrinsicBoundarySpeed N.metric 1 (gamma s 0) * |deriv gamma s 0| ≤
      intrinsicBoundarySpeed N.metric 2 s := by
  have hchain : HasDerivAt (e ∘ gamma) (fderiv ℝ e (gamma s) (deriv gamma s)) s :=
    he.hasFDerivAt.comp_hasDerivAt s hg.hasDerivAt
  have hd : fderiv ℝ e (gamma s) (deriv gamma s) =
      curveVelocity (n := 2) (intrinsicAnnulusBoundary 2) s := by
    rw [m64Intrinsic_curveVelocity_eq_deriv]
    exact (hchain.congr_of_eventuallyEq hlift.symm).deriv.symm
  have h := hbound (deriv gamma s)
  have hpoint : e (gamma s) = intrinsicAnnulusBoundary 2 s := hlift.self_of_nhds
  change c ^ 2 * ((intrinsicBoundarySpeed N.metric 1 (gamma s 0)) ^ 2 *
      (deriv gamma s 0) ^ 2 + (deriv gamma s 1) ^ 2) ≤
    N.metric.euclideanCoefficients (e (gamma s))
      (fderiv ℝ e (gamma s) (deriv gamma s))
      (fderiv ℝ e (gamma s) (deriv gamma s)) at h
  rw [hd, hpoint] at h
  unfold intrinsicBoundarySpeed RiemannianMetric.tangentNorm
  apply Real.le_sqrt_of_sq_le
  have hdiscard : 0 ≤ c ^ 2 * (deriv gamma s 1) ^ 2 :=
    mul_nonneg (sq_nonneg c) (sq_nonneg _)
  change (c * intrinsicBoundarySpeed N.metric 1 (gamma s 0) * |deriv gamma s 0|) ^ 2 ≤
    N.metric.euclideanCoefficients (intrinsicAnnulusBoundary 2 s)
      (curveVelocity (n := 2) (intrinsicAnnulusBoundary 2) s)
      (curveVelocity (n := 2) (intrinsicAnnulusBoundary 2) s)
  rw [mul_pow, mul_pow, sq_abs]
  nlinarith only [h, hdiscard]




theorem m64Intrinsic_normal_coordinate_differential
    {u : ℝ × ℝ → AnnulusCoordinates} {a t : ℝ}
    (hu : DifferentiableAt ℝ u (a, t)) (v : AnnulusCoordinates) :
    fderiv ℝ (fun z : AnnulusCoordinates => u (z 0, z 1)) !₂[a, t] v =
      fderiv ℝ u (a, t) (v 0, v 1) := by
  let P : AnnulusCoordinates → ℝ × ℝ := fun z => (z 0, z 1)
  have hP : HasFDerivAt P
      ((PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0).prod
        (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1)) !₂[a, t] :=
    (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 !₂[a, t] 0).prodMk
      (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 !₂[a, t] 1)
  have hchain := hu.hasFDerivAt.comp !₂[a, t] hP
  change fderiv ℝ (u ∘ P) !₂[a, t] v = fderiv ℝ u (a, t) (v 0, v 1)
  rw [hchain.fderiv]
  rfl





theorem m64Intrinsic_exists_normal_endpoint_lift
    (N : IntrinsicAnnulus) {u : ℝ × ℝ → AnnulusCoordinates}
    (hu : ContDiff ℝ ∞ u) {a t b c : ℝ}
    (hi : Function.Injective (fderiv ℝ u (a, t)))
    (hend : u (a, t) = intrinsicAnnulusBoundary 2 b)
    (hbound : ∀ v : ℝ × ℝ,
      c ^ 2 * ((intrinsicBoundarySpeed N.metric 1 a) ^ 2 * v.1 ^ 2 + v.2 ^ 2) ≤
        N.metric.inner (u (a, t)) (fderiv ℝ u (a, t) v) (fderiv ℝ u (a, t) v)) :
    ∃ (J : Set ℝ) (gamma : ℝ → AnnulusCoordinates),
      IsOpen J ∧ b ∈ J ∧ ContDiffOn ℝ ∞ gamma J ∧ gamma b = !₂[a, t] ∧
      (∀ s ∈ J, u (gamma s 0, gamma s 1) = intrinsicAnnulusBoundary 2 s) ∧
      c * intrinsicBoundarySpeed N.metric 1 a * |deriv gamma b 0| ≤
        intrinsicBoundarySpeed N.metric 2 b := by
  let e : AnnulusCoordinates → AnnulusCoordinates := fun z => u (z 0, z 1)
  have he : ContDiff ℝ ∞ e := hu.comp (by fun_prop)
  have hdu := hu.differentiable (by simp) (a, t)
  have hde (v : AnnulusCoordinates) :
      fderiv ℝ e !₂[a, t] v = fderiv ℝ u (a, t) (v 0, v 1) :=
    m64Intrinsic_normal_coordinate_differential hdu v
  have hei : Function.Injective (mfderiv (𝓡 2) (𝓡 2) e !₂[a, t]) := by
    rw [mfderiv_eq_fderiv]
    change Function.Injective (fderiv ℝ e !₂[a, t])
    intro v w hvw
    have hcoords := hi (by simpa only [hde] using hvw)
    ext i
    fin_cases i
    · exact congrArg Prod.fst hcoords
    · exact congrArg Prod.snd hcoords
  obtain ⟨J, gamma, hJ, hb, hgamma, hbase, _, hlift⟩ :=
    m64Intrinsic_exists_local_lifted_boundary isOpen_univ
      (contMDiff_iff_contDiff.mpr he).contMDiffOn (mem_univ !₂[a, t]) hei hend
  refine ⟨J, gamma, hJ, hb, hgamma, hbase, hlift, ?_⟩
  have hgamma' := (hgamma.contDiffAt (hJ.mem_nhds hb)).differentiableAt (by simp)
  have hevent : (e ∘ gamma) =ᶠ[𝓝 b] intrinsicAnnulusBoundary 2 := by
    filter_upwards [hJ.mem_nhds hb] with s hs
    exact hlift s hs
  have h := m64Intrinsic_boundary_lift_speed_le N (he.differentiable (by simp) _)
    hgamma' hevent (c := c) ?_
  · simpa only [hbase, Matrix.cons_val_zero] using h
  · intro v
    rw [hbase, hde]
    exact hbound (v 0, v 1)

end PoincareConjecture
