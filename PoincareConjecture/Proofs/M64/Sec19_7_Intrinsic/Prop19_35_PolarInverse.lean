import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ContinuedPolar
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RadialEndpoint
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem m64Intrinsic_exists_smooth_polar_inverse
    {e : AnnulusCoordinates → AnnulusCoordinates} {U : Set AnnulusCoordinates}
    (hU : IsOpen U) (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e U)
    {x : AnnulusCoordinates} (hx : x ∈ U)
    (hi : Function.Injective (mfderiv (𝓡 2) (𝓡 2) e x)) :
    ∃ F : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates,
      x ∈ F.source ∧ F.source ⊆ U ∧ (F : AnnulusCoordinates → AnnulusCoordinates) = e ∧
      ContDiffOn ℝ ∞ F F.source ∧ ContDiffOn ℝ ∞ F.symm F.target := by
  have hf : ContDiffAt ℝ ∞ e x := contMDiffAt_iff_contDiffAt.mp
    (he.contMDiffAt (hU.mem_nhds hx))
  have hif : Function.Injective (fderiv ℝ e x) := by
    simpa only [TangentSpace, mfderiv_eq_fderiv] using hi
  let A : AnnulusCoordinates ≃L[ℝ] AnnulusCoordinates :=
    (LinearEquiv.ofBijective (fderiv ℝ e x).toLinearMap
      ⟨hif, (LinearMap.injective_iff_surjective (f := (fderiv ℝ e x).toLinearMap)).mp
        hif⟩).toContinuousLinearEquiv
  have hA : A.toContinuousLinearMap = fderiv ℝ e x := rfl
  have hfd : ContinuousAt (fderiv ℝ e) x :=
    (hf.fderiv_right (m := 0) (by simp)).continuousAt
  have hinvertible : {v : AnnulusCoordinates | ∃ B : AnnulusCoordinates ≃L[ℝ]
      AnnulusCoordinates, B.toContinuousLinearMap = fderiv ℝ e v} ∈ 𝓝 x := by
    have h := A.nhds
    rw [hA] at h
    exact hfd.preimage_mem_nhds h
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (hU.mem_nhds hx) hinvertible)
  have hderiv : HasFDerivAt e A.toContinuousLinearMap x := by
    rw [hA]
    exact (hf.differentiableAt (by simp)).hasFDerivAt
  let H := hf.toOpenPartialHomeomorph e hderiv (by simp)
  let F := H.restrOpen (Metric.ball x r) Metric.isOpen_ball
  have hsource : F.source ⊆ U := fun v hv => (hsub hv.2).1
  have hF : (F : AnnulusCoordinates → AnnulusCoordinates) = e := rfl
  refine ⟨F, ⟨hf.mem_toOpenPartialHomeomorph_source hderiv (by simp),
    Metric.mem_ball_self hr⟩, hsource, hF, he.contDiffOn.mono hsource, ?_⟩
  intro y hy
  have hys := F.map_target hy
  obtain ⟨B, hB⟩ := (hsub hys.2).2
  have hsmooth : ContDiffAt ℝ ∞ F (F.symm y) :=
    (he.contDiffOn.contDiffAt (hU.mem_nhds (hsource hys)))
  have hD : HasFDerivAt F B.toContinuousLinearMap (F.symm y) := by
    rw [hB]
    exact (hsmooth.differentiableAt (by simp)).hasFDerivAt
  exact (F.contDiffAt_symm hy hD hsmooth).contDiffWithinAt

theorem m64Intrinsic_exists_local_lifted_boundary
    {e : AnnulusCoordinates → AnnulusCoordinates} {U : Set AnnulusCoordinates}
    (hU : IsOpen U) (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e U)
    {x : AnnulusCoordinates} (hx : x ∈ U)
    (hi : Function.Injective (mfderiv (𝓡 2) (𝓡 2) e x))
    {radius a : ℝ} (hpoint : e x = intrinsicAnnulusBoundary radius a) :
    ∃ (J : Set ℝ) (u : ℝ → AnnulusCoordinates),
      IsOpen J ∧ a ∈ J ∧ ContDiffOn ℝ ∞ u J ∧ u a = x ∧ MapsTo u J U ∧
      ∀ s ∈ J, e (u s) = intrinsicAnnulusBoundary radius s := by
  obtain ⟨F, hxF, hFU, hF, _, hFi⟩ := m64Intrinsic_exists_smooth_polar_inverse hU he hx hi
  let J := intrinsicAnnulusBoundary radius ⁻¹' F.target
  let u := F.symm ∘ intrinsicAnnulusBoundary radius
  have hboundary := m64Intrinsic_contDiff_boundary radius
  have ha : a ∈ J := by
    change intrinsicAnnulusBoundary radius a ∈ F.target
    rw [show intrinsicAnnulusBoundary radius a = F x by simpa only [hF] using hpoint.symm]
    exact F.map_source hxF
  refine ⟨J, u, F.open_target.preimage hboundary.continuous, ha,
    hFi.comp hboundary.contDiffOn (fun _ hs => hs), ?_, ?_, ?_⟩
  · change F.symm (intrinsicAnnulusBoundary radius a) = x
    rw [← hpoint, ← hF]
    exact F.left_inv hxF
  · intro s hs
    exact hFU (F.map_target hs)
  · intro s hs
    rw [← hF]
    exact F.right_inv hs

end PoincareConjecture
