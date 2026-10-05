import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Imports
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Blowup.OrdinaryRealization.SliceScalarEvolution
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Blowup.ScalarOperators.ScalarOperatorPullback
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Blowup.Transport.TransportedCapDistance
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Blowup.OrdinaryRealization.SliceNeckGeometry
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Tensor.HessianTrace

/-!
# Exact cap geometry on the actual Chapter 11 slice

Morgan-Tian Definition 9.72 and Theorem 12.28, pp. 323-324.
The genuine slice diffeomorphism preserves scalar suprema, the actual
curvature balls, scalar gradient norm, and full neck pullbacks. Its
unit speed comparison retains every strict intrinsic diameter bound.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace PoincareMT.M35.OrdinaryRealization

/-- Definition 9.72: the literal scalar supremum is unchanged
on the exact image set under the valid-slice identification. -/
theorem slice_scalarSup_image (P : M35StandardCapPredecessors)
    {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J) {t : ℝ} (ht : t ∈ J)
    (U : Set StandardCapSpace) :
    scalarCurvatureSupOn (metric F t) (connection F t) ((sliceDiffeomorph ht).symm '' U) =
      scalarCurvatureSupOn (F.metric t) (F.connection t) U := by
  unfold scalarCurvatureSupOn
  congr 1
  ext a
  constructor
  · rintro ⟨⟨_, ⟨x, hx, rfl⟩⟩, ha⟩
    exact ⟨⟨x, hx⟩, (scalar_eq P F ht x).symm.trans ha⟩
  · rintro ⟨⟨x, hx⟩, ha⟩
    exact ⟨⟨(sliceDiffeomorph ht).symm x, ⟨x, hx, rfl⟩⟩,
      (scalar_eq P F ht x).trans ha⟩

/-- Definition 9.72: the actual metric ball is exactly the
image of the original ball, including its original numerical radius. -/
theorem slice_ball_image (P : M35StandardCapPredecessors)
    {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J) {t : ℝ} (ht : t ∈ J)
    (x : StandardCapSpace) (r : ℝ) :
    (sliceDiffeomorph ht).symm '' (F.metric t).ball x r =
      (metric F t).ball ((sliceDiffeomorph ht).symm x) r := by
  let e := sliceDiffeomorph ht
  have heq (a b : StandardCapSpace) : (metric F t).edist (e.symm a) (e.symm b) =
      (F.metric t).edist a b := edist_eq P F ht a b
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    change (metric F t).edist (e.symm x) (e.symm z) < ENNReal.ofReal r
    rw [heq]
    exact hz
  · intro hy
    refine ⟨e y, ?_, e.symm_apply_apply y⟩
    change (F.metric t).edist x (e y) < ENNReal.ofReal r
    rw [← heq]
    change (metric F t).edist (e.symm x) y < ENNReal.ofReal r at hy
    simpa only [e.symm_apply_apply] using hy

/-- Definition 9.72: closure and compactness of each core ball
transport through the global valid-slice diffeomorphism. -/
theorem slice_closure_ball_image (P : M35StandardCapPredecessors)
    {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J) {t : ℝ} (ht : t ∈ J)
    (x : StandardCapSpace) (r : ℝ) :
    (sliceDiffeomorph ht).symm '' closure ((F.metric t).ball x r) =
      closure ((metric F t).ball ((sliceDiffeomorph ht).symm x) r) := by
  calc
    _ = closure ((sliceDiffeomorph ht).symm '' (F.metric t).ball x r) :=
      (sliceDiffeomorph ht).symm.toHomeomorph.image_closure _
    _ = _ := congrArg closure (slice_ball_image P F ht x r)

/-- Definition 9.72: the full frozen scalar-gradient supremum
is preserved under the actual unit-scale slice identification. -/
theorem slice_scalarGradientNorm_eq (P : M35StandardCapPredecessors)
    {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J) {t : ℝ} (ht : t ∈ J)
    (x : StandardCapSpace) :
    scalarGradientNorm (metric F t) (connection F t) ((sliceDiffeomorph ht).symm x) =
      scalarGradientNorm (F.metric t) (F.connection t) x := by
  exact (scalarGradientNorm_eq_pullback_of_scalar_germ (F.connection t) (connection F t)
    (sliceDiffeomorph ht).symm.contMDiffAt
    (M13.diffeomorph_mfderiv_isInvertible (sliceDiffeomorph ht).symm x)
    (fun v w => (metric_pullback F ht x v w).symm)
    (Proofs.M09.scalarCurvature_contMDiff P.curvature (connection F t)).contMDiffAt
    (Eventually.of_forall (fun y => (scalar_eq P F ht y).symm))).symm

/-- Definition 9.72: the image has no larger intrinsic diameter,
so each original strict supremum bound remains strictly valid. -/
theorem slice_intrinsicDiameter_image_le
    {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J) {t : ℝ} (ht : t ∈ J)
    {U : Set StandardCapSpace} (hU : IsOpen U) :
    intrinsicDiameter (metric F t) ((sliceDiffeomorph ht).symm '' U) ≤
      intrinsicDiameter (F.metric t) U := by
  have h := intrinsicDiameter_image_le (F.metric t) (metric F t)
    (sliceDiffeomorph ht).symm hU (sliceDiffeomorph ht).symm.contMDiff.contMDiffOn
    (C := 1) zero_lt_one (fun x _ v => by
      change Real.sqrt ((metric F t).inner ((sliceDiffeomorph ht).symm x)
        (mfderiv (𝓡 3) (𝓡 3) (sliceDiffeomorph ht).symm x v)
        (mfderiv (𝓡 3) (𝓡 3) (sliceDiffeomorph ht).symm x v)) ≤
          1 * Real.sqrt ((F.metric t).inner x v v)
      rw [metric_pullback, one_mul])
  simpa only [ENNReal.ofReal_one, one_mul] using h

/-- Definition 2.16: the complete total neck pullback is unchanged
under the slice identification, even outside its smooth spatial domain. -/
theorem slice_roundCylinderPullback
    {J : Set ℝ} (F : RicciFlow 3 StandardCapSpace J) {t : ℝ} (ht : t ∈ J)
    (coordinate : RoundCylinderSpace → StandardCapSpace) :
    roundCylinderPullback (metric F t) ((sliceDiffeomorph ht).symm ∘ coordinate) =
      roundCylinderPullback (F.metric t) coordinate := by
  funext z v w
  unfold roundCylinderPullback
  rw [(sliceDiffeomorph ht).symm.mfderiv_comp (by simp)]
  exact metric_pullback F ht (coordinate z)
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) coordinate z v)
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) coordinate z w)

end PoincareMT.M35.OrdinaryRealization
