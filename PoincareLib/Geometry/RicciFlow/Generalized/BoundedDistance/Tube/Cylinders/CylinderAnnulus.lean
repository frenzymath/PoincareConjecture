import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.CompactGeometry.CompactRegions
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.Algebra.SMul

/-!
# Literal annulus coordinates for compact confinement

Claim 10.3 of Morgan--Tian, pp. 248-249, uses separation by spheres isotopic
to a cylinder cross-section. The radial formulas below place the actual
open cylinder in Euclidean space for the compact ambient displacement
argument. See the M28 confinement-annulus derivation. This is unrelated to
the curvature cone constructed later in Section 10.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M28

private abbrev E := EuclideanSpace ℝ (Fin 3)
private abbrev CylI := (𝓡 2).prod 𝓘(ℝ, ℝ)

private instance : Fact (Module.finrank ℝ E = 2 + 1) := ⟨by simp⟩

/-- One fixed annulus, used only for the confinement isotopy. -/
def cylinderAnnulus : TopologicalSpace.Opens E :=
  ⟨{v | 1 < ‖v‖ ∧ ‖v‖ < 2},
    (isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)⟩

/-- The radial realization of the literal sphere-times-line cylinder. -/
def cylinderRadial (z : RoundCylinderSpace) : E :=
  (1 + z.2) • (z.1 : E)

/-- The radial coordinate is the original cylinder height plus one. -/
theorem cylinderRadial_norm {z : RoundCylinderSpace} (hz : 0 < z.2) :
    ‖cylinderRadial z‖ = 1 + z.2 := by
  have hq : ‖(z.1 : E)‖ = 1 := by simp
  simp only [cylinderRadial, norm_smul, hq, mul_one, Real.norm_eq_abs]
  exact abs_of_pos (by linarith)

/-- Valid open-cylinder points land in the fixed annulus. -/
theorem cylinderRadial_mem {z : RoundCylinderSpace} (hz : z.2 ∈ Ioo (0 : ℝ) 1) :
    cylinderRadial z ∈ cylinderAnnulus := by
  change 1 < ‖cylinderRadial z‖ ∧ ‖cylinderRadial z‖ < 2
  rw [cylinderRadial_norm hz.1]
  constructor <;> linarith [hz.1, hz.2]

/-- The literal radial formula is smooth on the whole sphere-times-line. -/
theorem contMDiff_cylinderRadial : ContMDiff CylI (𝓡 3) ∞ cylinderRadial := by
  have hs : ContMDiff (𝓡 2) (𝓡 3) ∞ (Subtype.val : UnitTwoSphere → E) :=
    contMDiff_coe_sphere
  have hq : ContMDiff CylI (𝓡 3) ∞ (fun z : RoundCylinderSpace => (z.1 : E)) :=
    hs.comp contMDiff_fst
  exact (contMDiff_const.add contMDiff_snd).smul hq

private theorem annulus_norm_pos (v : cylinderAnnulus) : 0 < ‖(v : E)‖ :=
  lt_trans zero_lt_one v.property.1

private theorem annulus_unit (v : cylinderAnnulus) :
    ‖(v : E)‖⁻¹ • (v : E) ∈ Metric.sphere (0 : E) 1 := by
  simp [norm_smul, (annulus_norm_pos v).ne']

/-- The inverse radial coordinates are evaluated only in the open annulus. -/
def cylinderAnnulusInverse (v : cylinderAnnulus) : RoundCylinderSpace :=
  (⟨‖(v : E)‖⁻¹ • (v : E), annulus_unit v⟩, ‖(v : E)‖ - 1)

/-- Inverse radial coordinates have the required strict axial bounds. -/
theorem cylinderAnnulusInverse_mem (v : cylinderAnnulus) :
    (cylinderAnnulusInverse v).2 ∈ Ioo (0 : ℝ) 1 := by
  change 0 < ‖(v : E)‖ - 1 ∧ ‖(v : E)‖ - 1 < 1
  constructor <;> linarith [v.property.1, v.property.2]

/-- The inverse radial formula retains the actual annulus point. -/
theorem cylinderRadial_annulusInverse (v : cylinderAnnulus) :
    cylinderRadial (cylinderAnnulusInverse v) = (v : E) := by
  simp [cylinderRadial, cylinderAnnulusInverse, smul_smul,
    (annulus_norm_pos v).ne']

/-- Radial realization retains both original cylinder coordinates. -/
theorem cylinderAnnulusInverse_radial {z : RoundCylinderSpace}
    (hz : z.2 ∈ Ioo (0 : ℝ) 1) :
    cylinderAnnulusInverse ⟨cylinderRadial z, cylinderRadial_mem hz⟩ = z := by
  have hp : 0 < 1 + z.2 := by linarith [hz.1]
  apply Prod.ext
  · apply Subtype.ext
    change ‖cylinderRadial z‖⁻¹ • cylinderRadial z = (z.1 : E)
    rw [cylinderRadial_norm hz.1]
    simp [cylinderRadial, smul_smul, hp.ne']
  · change ‖cylinderRadial z‖ - 1 = z.2
    rw [cylinderRadial_norm hz.1]
    ring

/-- Normalization is smooth on the actual annulus, which avoids zero. -/
theorem contMDiff_cylinderAnnulusInverse :
    ContMDiff (𝓡 3) CylI ∞ cylinderAnnulusInverse := by
  have hn : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞
      (fun v : cylinderAnnulus => ‖(v : E)‖) := by
    intro v
    exact (contDiffAt_norm ℝ (norm_pos_iff.mp (annulus_norm_pos v))).contMDiffAt.comp v
      (contMDiff_subtype_val (I := 𝓡 3) (U := cylinderAnnulus) v)
  have hvec : ContMDiff (𝓡 3) (𝓡 3) ∞
      (fun v : cylinderAnnulus => ‖(v : E)‖⁻¹ • (v : E)) :=
    (hn.inv₀ (fun v => (annulus_norm_pos v).ne')).smul
      (contMDiff_subtype_val (I := 𝓡 3) (U := cylinderAnnulus))
  have hq : ContMDiff (𝓡 3) (𝓡 2) ∞
      (fun v : cylinderAnnulus => (⟨‖(v : E)‖⁻¹ • (v : E), annulus_unit v⟩ :
        UnitTwoSphere)) := hvec.codRestrict_sphere annulus_unit
  exact hq.prodMk (hn.sub contMDiff_const)

end PoincareMT.M28

namespace PoincareMT.OpenCylinderModel

open M28

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {U : TopologicalSpace.Opens M}

/-- The original cylinder's map into the fixed Euclidean annulus. -/
def annulusCoordinates (T : OpenCylinderModel (U : Set M)) (x : U) :
    EuclideanSpace ℝ (Fin 3) := cylinderRadial (T.inverse x)

/-- The original carrier maps into the fixed annulus. -/
theorem annulusCoordinates_mem (T : OpenCylinderModel (U : Set M)) (x : U) :
    T.annulusCoordinates x ∈ cylinderAnnulus :=
  cylinderRadial_mem (T.inverse_mem x x.property).2

/-- The inverse uses the original literal cylinder coordinate map. -/
def annulusParametrization (T : OpenCylinderModel (U : Set M))
    (v : cylinderAnnulus) : M := T.coordinate (cylinderAnnulusInverse v)

/-- The inverse annulus map lands in the original open carrier. -/
theorem annulusParametrization_mem (T : OpenCylinderModel (U : Set M))
    (v : cylinderAnnulus) : T.annulusParametrization v ∈ U :=
  T.coordinate_mem_m28 (cylinderAnnulusInverse_mem v)

/-- The displayed maps recover the exact original carrier point. -/
theorem annulusParametrization_coordinates (T : OpenCylinderModel (U : Set M))
    (x : U) :
    T.annulusParametrization ⟨T.annulusCoordinates x, T.annulusCoordinates_mem x⟩ = x := by
  change T.coordinate (cylinderAnnulusInverse
    ⟨cylinderRadial (T.inverse x), _⟩) = x
  rw [cylinderAnnulusInverse_radial (T.inverse_mem x x.property).2]
  exact T.right_inverse x.property

/-- The displayed maps recover the exact original annulus point. -/
theorem annulusCoordinates_parametrization (T : OpenCylinderModel (U : Set M))
    (v : cylinderAnnulus) :
    T.annulusCoordinates ⟨T.annulusParametrization v, T.annulusParametrization_mem v⟩ = v := by
  change cylinderRadial (T.inverse (T.coordinate (cylinderAnnulusInverse v))) = v
  rw [T.left_inverse ⟨mem_univ _, cylinderAnnulusInverse_mem v⟩]
  exact cylinderRadial_annulusInverse v

/-- Smoothness uses the frozen cylinder inverse on its true carrier. -/
theorem contMDiff_annulusCoordinates (T : OpenCylinderModel (U : Set M)) :
    ContMDiff (𝓡 3) (𝓡 3) ∞ T.annulusCoordinates := by
  exact contMDiff_cylinderRadial.comp
    (T.inverse_smooth.comp_contMDiff
      (contMDiff_subtype_val (I := 𝓡 3) (U := U)) (fun x => x.property))

/-- Smoothness uses the frozen cylinder coordinate on its true strip. -/
theorem contMDiff_annulusParametrization (T : OpenCylinderModel (U : Set M)) :
    ContMDiff (𝓡 3) (𝓡 3) ∞ T.annulusParametrization := by
  exact T.coordinate_smooth.comp_contMDiff contMDiff_cylinderAnnulusInverse
    (fun v => ⟨mem_univ _, cylinderAnnulusInverse_mem v⟩)

/-- The actual cylinder and annulus are homeomorphic by the displayed maps. -/
def annulusHomeomorph (T : OpenCylinderModel (U : Set M)) : U ≃ₜ cylinderAnnulus where
  toFun x := ⟨T.annulusCoordinates x, T.annulusCoordinates_mem x⟩
  invFun v := ⟨T.annulusParametrization v, T.annulusParametrization_mem v⟩
  left_inv x := Subtype.ext (T.annulusParametrization_coordinates x)
  right_inv v := Subtype.ext (T.annulusCoordinates_parametrization v)
  continuous_toFun := T.contMDiff_annulusCoordinates.continuous.subtype_mk _
  continuous_invFun := T.contMDiff_annulusParametrization.continuous.subtype_mk _

/-- A total inverse readout for ambient cutoffs; its exterior values are
irrelevant and no exterior regularity is asserted. -/
def annulusAmbientInverse (T : OpenCylinderModel (U : Set M))
    (v : EuclideanSpace ℝ (Fin 3)) : M := by
  classical
  exact if hv : v ∈ cylinderAnnulus then T.annulusParametrization ⟨v, hv⟩
    else T.coordinate (⟨EuclideanSpace.basisFun (Fin 3) ℝ 0, by simp⟩, 0)

/-- The total inverse agrees exactly with the annulus parametrization. -/
theorem annulusAmbientInverse_apply (T : OpenCylinderModel (U : Set M))
    (v : cylinderAnnulus) : T.annulusAmbientInverse v = T.annulusParametrization v := by
  simp only [annulusAmbientInverse, dif_pos v.property]

/-- The total inverse is smooth on the annulus, the only domain used. -/
theorem contMDiffOn_annulusAmbientInverse (T : OpenCylinderModel (U : Set M)) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ T.annulusAmbientInverse
      (cylinderAnnulus : Set (EuclideanSpace ℝ (Fin 3))) := by
  have h : ContMDiff (𝓡 3) (𝓡 3) ∞
      (fun v : cylinderAnnulus => T.annulusAmbientInverse v) := by
    convert T.contMDiff_annulusParametrization using 1
    funext v
    exact T.annulusAmbientInverse_apply v
  intro v hv
  exact (contMDiffAt_subtype_iff.mp (h ⟨v, hv⟩)).contMDiffWithinAt

end PoincareMT.OpenCylinderModel
