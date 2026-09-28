import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_TransverseEquation
import Mathlib.Analysis.Calculus.Deriv.Shift

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture

open ConnectionVariation

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem m64Intrinsic_curveVelocity_comp_add_const
    (gamma : ℝ → AnnulusCoordinates) (a t : ℝ) :
    curveVelocity (n := 2) (fun s => gamma (s + a)) t =
      curveVelocity (n := 2) gamma (t + a) := by
  rw [m64Intrinsic_curveVelocity_eq_deriv, m64Intrinsic_curveVelocity_eq_deriv,
    deriv_comp_add_const]

theorem m64Intrinsic_variation_intrinsic_jacobi
    (N : IntrinsicAnnulus) {u : ℝ × ℝ → AnnulusCoordinates}
    {S I : Set ℝ} (hS : IsOpen S) (hI : IsOpen I)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ u (S ×ˢ I))
    (hgeo : ∀ s ∈ S, N.metric.IsGeodesicOn (fun t => u (s, t)) I)
    {a t : ℝ} (ha : a ∈ S) (ht : t ∈ I) :
    let q : ℝ → AnnulusCoordinates := fun r => u (a, r)
    let X : ℝ → AnnulusCoordinates := fun r =>
      curveVelocity (n := 2) (fun s => u (s, r)) a
    manifoldCovDerivAlong N.metric q (manifoldCovDerivAlong N.metric q X 1) 1 t =
      -N.connection.curvature (q t) (X t)
        (curveVelocity (n := 2) q t) (curveVelocity (n := 2) q t) := by
  let S' : Set ℝ := (fun s : ℝ => s + a) ⁻¹' S
  let shift : ℝ × ℝ → ℝ × ℝ := fun p => (p.1 + a, p.2)
  have hS' : IsOpen S' := hS.preimage (continuous_id.add continuous_const)
  have hzero : (0 : ℝ) ∈ S' := by simpa only [S', mem_preimage, zero_add] using ha
  have hshift : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ shift :=
    contMDiff_iff_contDiff.mpr (by dsimp only [shift]; fun_prop)
  have hshifted : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ (u ∘ shift) (S' ×ˢ I) :=
    hu.comp hshift.contMDiffOn (fun p hp => ⟨hp.1, hp.2⟩)
  have hgeo' : ∀ s ∈ S', N.metric.IsGeodesicOn (fun r => (u ∘ shift) (s, r)) I :=
    fun s hs => hgeo (s + a) hs
  have h := manifoldVariation_jacobi N.metric N.connection
    hS' hI hzero hshifted hgeo' ht
  change manifoldCovDerivAlong N.metric (fun r => u (0 + a, r))
    (manifoldCovDerivAlong N.metric (fun r => u (0 + a, r))
      (fun r => curveVelocity (n := 2) (fun s => u (s + a, r)) 0) 1) 1 t +
    N.connection.curvature (u (0 + a, t))
      (curveVelocity (n := 2) (fun s => u (s + a, t)) 0)
      (curveVelocity (n := 2) (fun r => u (0 + a, r)) t)
      (curveVelocity (n := 2) (fun r => u (0 + a, r)) t) = 0 at h
  have hfield : (fun r => curveVelocity (n := 2) (fun s => u (s + a, r)) 0) =
      (fun r => curveVelocity (n := 2) (fun s => u (s, r)) a) := by
    funext r
    exact (m64Intrinsic_curveVelocity_eq_deriv (fun s => u (s + a, r)) 0).trans
      ((deriv_comp_add_const (fun s => u (s, r)) a 0).trans
        ((congrArg (deriv (fun s => u (s, r))) (zero_add a)).trans
          (m64Intrinsic_curveVelocity_eq_deriv (fun s => u (s, r)) a).symm))
  erw [zero_add, hfield] at h
  erw [congrFun hfield t] at h
  exact eq_neg_of_add_eq_zero_left h

theorem m64Intrinsic_contDiff_variation_field
    {u : ℝ × ℝ → AnnulusCoordinates} {S I : Set ℝ}
    (hS : IsOpen S) (hI : IsOpen I) (hu : ContDiffOn ℝ ∞ u (S ×ˢ I))
    {a t : ℝ} (ha : a ∈ S) (ht : t ∈ I) :
    ContDiffAt ℝ ∞ (fun r => curveVelocity (n := 2) (fun s => u (s, r)) a) t := by
  let F : ℝ → AnnulusCoordinates := fun r => fderiv ℝ u (a, r) (1, 0)
  have huat := hu.contDiffAt ((hS.prod hI).mem_nhds
    (show (a, t) ∈ S ×ˢ I from ⟨ha, ht⟩))
  have hF : ContDiffAt ℝ ∞ F t :=
    (((huat.fderiv_right (m := ∞) (by simp)).comp t (by fun_prop)).clm_apply contDiffAt_const)
  have heq : (fun r => curveVelocity (n := 2) (fun s => u (s, r)) a) =ᶠ[𝓝 t] F := by
    filter_upwards [hI.mem_nhds ht] with r hr
    have hd := ((hu.contDiffAt ((hS.prod hI).mem_nhds ⟨ha, hr⟩)).differentiableAt
      (by simp)).hasFDerivAt.comp_hasDerivAt (l := u) (f := fun s => (s, r)) a
        ((hasDerivAt_id a).prodMk (hasDerivAt_const a r))
    rw [m64Intrinsic_curveVelocity_eq_deriv]
    exact hd.deriv
  exact hF.congr_of_eventuallyEq heq

end PoincareConjecture
