import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_EndpointLift
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff













noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace




theorem m64Intrinsic_exists_normal_local_chart
    {u : ℝ × ℝ → AnnulusCoordinates} (hu : ContDiff ℝ ∞ u)
    {a t : ℝ} (hi : Function.Injective (fderiv ℝ u (a, t))) :
    ∃ F : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates,
      !₂[a, t] ∈ F.source ∧
        (F : AnnulusCoordinates → AnnulusCoordinates) =
          (fun z => u (z 0, z 1)) ∧
        ContDiffOn ℝ ∞ F F.source ∧
        ContDiffOn ℝ ∞ F.symm F.target := by
  let e : AnnulusCoordinates → AnnulusCoordinates := fun z => u (z 0, z 1)
  have he : ContDiff ℝ ∞ e := hu.comp (by fun_prop)
  have hdu := hu.differentiable (by simp) (a, t)
  have hde (v : AnnulusCoordinates) :
      fderiv ℝ e !₂[a, t] v = fderiv ℝ u (a, t) (v 0, v 1) :=
    m64Intrinsic_normal_coordinate_differential hdu v
  have heinj : Function.Injective (fderiv ℝ e !₂[a, t]) := by
    intro v w hvw
    have hcoords := hi (by simpa only [hde] using hvw)
    ext i
    fin_cases i
    · exact congrArg Prod.fst hcoords
    · exact congrArg Prod.snd hcoords
  let A : AnnulusCoordinates ≃L[ℝ] AnnulusCoordinates :=
    (LinearEquiv.ofBijective (fderiv ℝ e !₂[a, t]).toLinearMap
      ⟨heinj,
        (LinearMap.injective_iff_surjective
          (f := (fderiv ℝ e !₂[a, t]).toLinearMap)).mp
          heinj⟩).toContinuousLinearEquiv
  have hA : A.toContinuousLinearMap = fderiv ℝ e !₂[a, t] := rfl
  have hfd : ContinuousAt (fderiv ℝ e) !₂[a, t] :=
    (he.contDiffAt.fderiv_right (m := 0) (by simp)).continuousAt
  have hinvertible : {v : AnnulusCoordinates | ∃ B : AnnulusCoordinates ≃L[ℝ]
      AnnulusCoordinates, B.toContinuousLinearMap = fderiv ℝ e v} ∈
      𝓝 !₂[a, t] := by
    have h := A.nhds
    rw [hA] at h
    exact hfd.preimage_mem_nhds h
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hinvertible
  have he0 : ContDiffAt ℝ ∞ e !₂[a, t] := he.contDiffAt
  have hderiv : HasFDerivAt e A.toContinuousLinearMap !₂[a, t] := by
    rw [hA]
    exact (he0.differentiableAt (by simp)).hasFDerivAt
  let H := he0.toOpenPartialHomeomorph e
    hderiv (by simp)
  let F := H.restrOpen (Metric.ball !₂[a, t] r) Metric.isOpen_ball
  have hsource : F.source ⊆ {v : AnnulusCoordinates | ∃ B :
      AnnulusCoordinates ≃L[ℝ] AnnulusCoordinates,
      B.toContinuousLinearMap = fderiv ℝ e v} := fun v hv => hsub hv.2
  have hF : (F : AnnulusCoordinates → AnnulusCoordinates) = e := rfl
  refine ⟨F, ⟨he0.mem_toOpenPartialHomeomorph_source hderiv (by simp),
      Metric.mem_ball_self hr⟩, hF, he.contDiffOn.mono (fun _ _ => mem_univ _), ?_⟩
  intro y hy
  have hys := F.map_target hy
  obtain ⟨B, hB⟩ := hsource hys
  have hsmooth : ContDiffAt ℝ ∞ F (F.symm y) :=
    he.contDiffAt
  have hD : HasFDerivAt F B.toContinuousLinearMap (F.symm y) := by
    rw [hB]
    exact (hsmooth.differentiableAt (by simp)).hasFDerivAt
  exact (F.contDiffAt_symm hy hD hsmooth).contDiffWithinAt

end PoincareConjecture
