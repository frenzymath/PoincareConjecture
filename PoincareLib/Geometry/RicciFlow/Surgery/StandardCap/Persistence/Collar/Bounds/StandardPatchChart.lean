import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.SourceNames.Metric
import PoincareLib.Geometry.RicciFlow.Surgery.Metric.Neck.CenteredNeckChart
import PoincareLib.Geometry.Riemannian.Coordinates.Coefficients
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Geometry
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Actual fixed charts on standard cylindrical patches

The primitive standard-cylinder patch is a partial diffeomorphism.
Composing it with the centered stereographic chart identifies its
literal pullback coefficients with the round-cylinder comparison field.
Morgan--Tian, Proposition 12.7 in Proposition 16.5, pp. 373-374;
see M44 derivation 42.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareMT.M44

open M36

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "IC" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

/-- The centered Euclidean cylinder chart, with its full actual
source and target. Source: Proposition 12.7; M44 derivation 42. -/
noncomputable def centeredCylinderChart (theta : UnitTwoSphere) (s : ℝ) :
    PartialDiffeomorph (𝓡 3) IC E RoundCylinderSpace ∞ where
  toFun := centeredCylinderLift theta s
  invFun z := cylinderEuclideanEquiv.symm ((chartAt E₂ theta) z.1, z.2 - s)
  source := univ
  target := (chartAt E₂ theta).source ×ˢ univ
  map_source' p _ := ⟨(chartAt E₂ theta).map_target (by
    rw [sphere_chart_target_univ]; exact mem_univ _), mem_univ _⟩
  map_target' _ _ := mem_univ _
  left_inv' p _ := by
    have hp : cylinderHorizontalProjection p ∈ (chartAt E₂ theta).target := by
      rw [sphere_chart_target_univ]
      exact mem_univ _
    simp only [centeredCylinderLift, (chartAt E₂ theta).right_inv hp, add_sub_cancel_right]
    exact cylinderEuclideanEquiv.symm_apply_apply p
  right_inv' z hz := by
    change ((chartAt E₂ theta).symm
      (cylinderEuclideanEquiv (cylinderEuclideanEquiv.symm
        ((chartAt E₂ theta) z.1, z.2 - s))).1,
      (cylinderEuclideanEquiv (cylinderEuclideanEquiv.symm
        ((chartAt E₂ theta) z.1, z.2 - s))).2 + s) = z
    rw [cylinderEuclideanEquiv.apply_symm_apply]
    simp only [(chartAt E₂ theta).left_inv hz.1, sub_add_cancel]
  open_source := isOpen_univ
  open_target := (chartAt E₂ theta).open_source.prod isOpen_univ
  contMDiffOn_toFun := (centeredCylinderLift_contMDiff theta s).contMDiffOn
  contMDiffOn_invFun := by
    intro z hz
    have hc := contMDiffAt_of_mem_maximalAtlas (I := 𝓡 2) (n := ∞)
      (IsManifold.chart_mem_maximalAtlas theta) hz.1
    have hfirst : ContMDiffAt IC (𝓡 2) ∞
        (fun q : RoundCylinderSpace => (chartAt E₂ theta) q.1) z :=
      hc.comp z contMDiffAt_fst
    have hsecond : ContMDiffAt IC 𝓘(ℝ, ℝ) ∞
        (fun q : RoundCylinderSpace => q.2 - s) z :=
      contMDiffAt_snd.sub contMDiffAt_const
    exact (cylinderEuclideanEquiv.symm.contDiff.contMDiff.contMDiffAt.comp z
      ((contMDiffAt_prod_module_iff _).mpr ⟨hfirst, hsecond⟩)).contMDiffWithinAt

/-- The supplied standard patch, with its primitive inverse, is
a partial diffeomorphism. Source: Proposition 12.7; M44 derivation 42. -/
noncomputable def standardPatchDiffeomorph {length : ℝ} {center : StandardCapSpace}
    (N : StandardCylinderPatch length center) :
    PartialDiffeomorph IC (𝓡 3) StandardCylinderSpace StandardCapSpace ∞ where
  toFun := N.coordinate
  invFun := N.inverse
  source := univ ×ˢ Ioo (-length) length
  target := N.carrier
  map_source' _ hz := N.coordinate_image ▸ mem_image_of_mem N.coordinate hz
  map_target' x hx := ⟨mem_univ _, N.inverse_domain x hx⟩
  left_inv' _ hz := N.coordinate_left_inverse hz
  right_inv' _ hx := N.coordinate_right_inverse hx
  open_source := isOpen_univ.prod isOpen_Ioo
  open_target := N.carrier_open
  contMDiffOn_toFun := N.coordinate_smooth
  contMDiffOn_invFun := N.inverse_smooth

/-- One fixed Euclidean chart of the actual standard patch.
Source: Proposition 12.7 in Proposition 16.5; M44 derivation 42. -/
noncomputable def centeredStandardPatchChart {length : ℝ} {center : StandardCapSpace}
    (N : StandardCylinderPatch length center) (theta : UnitTwoSphere) (s : ℝ) :
    PartialDiffeomorph (𝓡 3) (𝓡 3) E StandardCapSpace ∞ :=
  (centeredCylinderChart theta s).trans (standardPatchDiffeomorph N)

/-- Membership in the actual chart source is the axial condition.
Source: Proposition 12.7; M44 derivation 42. -/
theorem mem_centeredStandardPatchChart_source {length : ℝ} {center : StandardCapSpace}
    (N : StandardCylinderPatch length center) (theta : UnitTwoSphere) (s : ℝ) (p : E) :
    p ∈ (centeredStandardPatchChart N theta s).source ↔
      cylinderHeightCovector p + s ∈ Ioo (-length) length := by
  change (p ∈ univ ∧ centeredCylinderLift theta s p ∈ univ ×ˢ Ioo (-length) length) ↔ _
  simp only [mem_univ, mem_prod, true_and, centeredCylinderLift]

/-- The centered source point maps to the literal cylinder point.
Source: Proposition 12.7; M44 derivation 42. -/
theorem centeredStandardPatchChart_zero {length : ℝ} {center : StandardCapSpace}
    (N : StandardCylinderPatch length center) (theta : UnitTwoSphere) (s : ℝ) :
    centeredStandardPatchChart N theta s 0 = N.coordinate (theta, s) := by
  change N.coordinate (centeredCylinderLift theta s 0) = _
  rw [centeredCylinderLift_zero]

/-- The actual pullback coefficients equal the centered intrinsic
comparison field throughout the open chart. Source: Proposition 12.7
in Proposition 16.5; M44 derivation 42. -/
theorem centeredStandardPatchChart_pullback {length : ℝ} {center : StandardCapSpace}
    (N : StandardCylinderPatch length center) (theta : UnitTwoSphere) (s : ℝ)
    (g : RiemannianMetric 3 StandardCapSpace) {p : E}
    (hp : p ∈ (centeredStandardPatchChart N theta s).source) :
    g.pullbackCoefficients (centeredStandardPatchChart N theta s) p =
      centeredCylinderMetric (roundCylinderPullback g N.coordinate) theta s p := by
  have hz : centeredCylinderLift theta s p ∈ univ ×ˢ Ioo (-length) length := hp.2
  have hN := (N.coordinate_smooth.contMDiffAt
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds hz)).mdifferentiableAt (by simp)
  have hL := (centeredCylinderLift_contMDiff theta s p).mdifferentiableAt (by simp)
  have hd (v : E) :
      mfderiv (𝓡 3) (𝓡 3) (centeredStandardPatchChart N theta s) p v =
        mfderiv IC (𝓡 3) N.coordinate (centeredCylinderLift theta s p)
          (mfderiv (𝓡 2) (𝓡 2) (chartAt E₂ theta).symm
            (cylinderHorizontalProjection p) (cylinderHorizontalProjection v),
            cylinderHeightCovector v) := by
    change mfderiv (𝓡 3) (𝓡 3) (N.coordinate ∘ centeredCylinderLift theta s) p v = _
    rw [mfderiv_comp p hN hL]
    change mfderiv IC (𝓡 3) N.coordinate (centeredCylinderLift theta s p)
      (mfderiv (𝓡 3) IC (centeredCylinderLift theta s) p v) = _
    rw [centeredCylinderLift_mfderiv]
  apply euclideanThree_bilinear_ext
  intro i j
  rw [centeredCylinderMetric, centeredCylinderBilinear_basis]
  have hcoord : cylinderEuclideanEquiv p + (0, s) =
      (cylinderHorizontalProjection p, cylinderHeightCovector p + s) := by
    exact Prod.ext (add_zero _) rfl
  rw [hcoord]
  change g.inner (centeredStandardPatchChart N theta s p)
      (mfderiv (𝓡 3) (𝓡 3) (centeredStandardPatchChart N theta s) p
        (EuclideanSpace.basisFun (Fin 3) ℝ i))
      (mfderiv (𝓡 3) (𝓡 3) (centeredStandardPatchChart N theta s) p
        (EuclideanSpace.basisFun (Fin 3) ℝ j)) = _
  rw [hd, hd]
  have hP (k : Fin 3) : cylinderHorizontalProjection (EuclideanSpace.basisFun (Fin 3) ℝ k) =
      (roundCylinderCoordinateBasis k).1 := congrArg Prod.fst (cylinderEuclideanEquiv_basis k)
  simp only [roundCylinderTensorCoefficient, roundCylinderPullback,
    cylinderHeightCovector_basis, hP]
  rfl

end PoincareMT.M44
