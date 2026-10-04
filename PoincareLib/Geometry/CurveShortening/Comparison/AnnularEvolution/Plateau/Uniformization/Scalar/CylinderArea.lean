import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Uniformization.Scalar.InverseFibers
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Uniformization.Scalar.OpenCylinder
import PoincareLib.Geometry.Riemannian.MinimalSurface.Sphere.Minimizer.Annular.Cap

/-!
# Area transport through the actual inverse cylinder chart

The inverse harmonic-coordinate chart covers the planar annulus once on
the half-open angular rectangle. Its literal Jacobian therefore transports
the original map's area, including its rank-deficient points.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareMT.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Cover" => ℝ × ℝ

/-- One literal cylinder fundamental domain, with the angular seam kept once and the two
radial boundary components omitted. Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449;
the explicit project construction is recorded in
`proof-work/tasks/M64/reports/annular-smooth-cover-chart.md`. -/
def scalarCylinderFundamental : Set Plane :=
  {p | p 1 ∈ Ioo (0 : ℝ) 1 ∧ p 0 ∈ Ico (0 : ℝ) curvePeriod}

/-- The actual inverse normalized chart in the annulus rectangle's angular-first
coordinates. Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449; the explicit project
construction is recorded in `proof-work/tasks/M64/reports/annular-smooth-cover-chart.md`. -/
def scalarInverseCylinderMap (e : OpenPartialHomeomorph Cover Cover) : Plane → Plane :=
  scalarInverseCoverMap e ∘ scalarCylinderCoordinate

private theorem period_pos : 0 < curvePeriod := by
  unfold curvePeriod
  positivity

/-- The actual half-open cylinder fundamental domain is measurable. Source: Morgan--Tian
(2007), Lemma 19.15, pp. 447-449; the explicit project construction is recorded in
`proof-work/tasks/M64/reports/annular-smooth-cover-chart.md`. -/
theorem scalarCylinderFundamental_measurable : MeasurableSet scalarCylinderFundamental :=
  (measurableSet_Ioo.preimage (EuclideanSpace.proj 1).continuous.measurable).inter
    (measurableSet_Ico.preimage (EuclideanSpace.proj 0).continuous.measurable)

/-- The angular-first rectangle coordinate maps into one exact half-open unit angular strip.
Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449; the explicit project construction is
recorded in `proof-work/tasks/M64/reports/annular-smooth-cover-chart.md`. -/
theorem scalarCylinderCoordinate_mem_fundamental {p : Plane}
    (hp : p ∈ scalarCylinderFundamental) :
    scalarCylinderCoordinate p ∈ scalarPotentialStrip ∩ {y | y.2 ∈ Ico (0 : ℝ) 1} := by
  refine ⟨hp.1, ?_, ?_⟩
  · exact mul_nonneg (inv_nonneg.mpr period_pos.le) hp.2.1
  · change curvePeriod⁻¹ * p 0 < 1
    rw [← inv_mul_cancel₀ period_pos.ne']
    exact mul_lt_mul_of_pos_left hp.2.2 (inv_pos.mpr period_pos)

/-- The genuine smooth inverse cover is smooth in angular-first cylinder coordinates on the
whole open radial strip. Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449; the explicit
project construction is recorded in
`proof-work/tasks/M64/reports/annular-smooth-cover-chart.md`. -/
theorem scalarInverseCylinderMap_smooth (e : OpenPartialHomeomorph Cover Cover)
    (htarget : e.target = scalarPotentialStrip)
    (hei : ContDiffOn ℝ ∞ e.symm e.target) :
    ContDiffOn ℝ ∞ (scalarInverseCylinderMap e) {p | p 1 ∈ Ioo (0 : ℝ) 1} := by
  intro p hp
  have hp' : scalarCylinderCoordinate p ∈ e.target := htarget ▸ hp
  exact (((scalarInverseCoverMap_smooth e hei).contDiffAt
    (e.open_target.mem_nhds hp')).comp p
    scalarCylinderCoordinate.contDiff.contDiffAt).contDiffWithinAt

/-- The inverse cylinder is injective on its actual half-open angular fundamental domain.
Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449; the explicit project construction is
recorded in `proof-work/tasks/M64/reports/annular-smooth-cover-chart.md`. -/
theorem scalarInverseCylinderMap_injOn_fundamental
    (e : OpenPartialHomeomorph Cover Cover)
    (hsource : e.source = scalarCoverStrip)
    (htarget : e.target = scalarPotentialStrip)
    (hdeck : ∀ z ∈ e.source, e (z + (0, 1)) = e z + (0, 1)) :
    InjOn (scalarInverseCylinderMap e) scalarCylinderFundamental := by
  intro p hp q hq hpq
  apply scalarCylinderCoordinate_injective
  apply scalarInverseCoverMap_injOn_fundamental e hsource hdeck 0
    (x₁ := scalarCylinderCoordinate p) (x₂ := scalarCylinderCoordinate q)
  · simpa only [htarget, zero_add] using scalarCylinderCoordinate_mem_fundamental hp
  · simpa only [htarget, zero_add] using scalarCylinderCoordinate_mem_fundamental hq
  · exact hpq

/-- The actual inverse cylinder fundamental domain covers the entire physical open annulus.
Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449; the explicit project construction is
recorded in `proof-work/tasks/M64/reports/annular-smooth-cover-chart.md`. -/
theorem scalarInverseCylinderMap_image_fundamental
    (e : OpenPartialHomeomorph Cover Cover)
    (hsource : e.source = scalarCoverStrip)
    (htarget : e.target = scalarPotentialStrip)
    (hdeck : ∀ z ∈ e.source, e (z + (0, 1)) = e z + (0, 1)) :
    scalarInverseCylinderMap e '' scalarCylinderFundamental = scalarAnnulus := by
  rw [scalarInverseCylinderMap, image_comp]
  have hcoord : scalarCylinderCoordinate '' scalarCylinderFundamental =
      scalarPotentialStrip ∩ {y | y.2 ∈ Ico (0 : ℝ) 1} := by
    apply Subset.antisymm
    · rintro _ ⟨p, hp, rfl⟩
      exact scalarCylinderCoordinate_mem_fundamental hp
    · intro y hy
      refine ⟨annulusPoint (curvePeriod * y.2) y.1, ?_,
        scalarCylinderCoordinate_right_inverse y⟩
      refine ⟨hy.1, ?_, ?_⟩
      · exact mul_nonneg period_pos.le hy.2.1
      · change curvePeriod * y.2 < curvePeriod
        simpa only [mul_one] using mul_lt_mul_of_pos_left hy.2.2 period_pos
  rw [hcoord, ← htarget]
  simpa only [zero_add] using scalarInverseCoverMap_image_fundamental
    e hsource htarget hdeck 0

section Area

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- The actual cylinder inverse preserves the literal area integral of every map smooth on
the planar annulus, without an immersion hypothesis. Source: Morgan--Tian (2007), Lemma
19.15, pp. 447-449; the explicit project construction is recorded in
`proof-work/tasks/M64/reports/annular-smooth-cover-chart.md`. -/
theorem scalarInverseCylinderMap_area (g : RiemannianMetric n M)
    {f : Plane → M} (hf : ContMDiffOn (𝓡 2) (𝓡 n) 1 f scalarAnnulus)
    (e : OpenPartialHomeomorph Cover Cover)
    (hsource : e.source = scalarCoverStrip)
    (htarget : e.target = scalarPotentialStrip)
    (hei : ContDiffOn ℝ ∞ e.symm e.target)
    (hdeck : ∀ z ∈ e.source, e (z + (0, 1)) = e z + (0, 1)) :
    (∫ p in scalarCylinderFundamental, m60AreaDensity g (f ∘ scalarInverseCylinderMap e) p) =
      ∫ x in scalarAnnulus, m60AreaDensity g f x := by
  let F := scalarInverseCylinderMap e
  have himage : F '' scalarCylinderFundamental = scalarAnnulus :=
    scalarInverseCylinderMap_image_fundamental e hsource htarget hdeck
  have hFd {p : Plane} (hp : p ∈ scalarCylinderFundamental) :
      DifferentiableAt ℝ F p := by
    apply ((scalarInverseCylinderMap_smooth e htarget hei).contDiffAt ?_).differentiableAt
      (by simp)
    exact (isOpen_Ioo.preimage (EuclideanSpace.proj 1).continuous).mem_nhds hp.1
  have hchange := integral_image_eq_integral_abs_det_fderiv_smul volume
    scalarCylinderFundamental_measurable
    (fun p hp => (hFd hp).hasFDerivAt.hasFDerivWithinAt)
    (scalarInverseCylinderMap_injOn_fundamental e hsource htarget hdeck)
    (m60AreaDensity g f)
  rw [himage] at hchange
  rw [hchange]
  apply setIntegral_congr_fun scalarCylinderFundamental_measurable
  intro p hp
  have hFp : F p ∈ scalarAnnulus := himage ▸ mem_image_of_mem F hp
  exact M60.suAreaDensity_comp_plane g
    ((hf.contMDiffAt (scalarAnnulus_isOpen.mem_nhds hFp)).mdifferentiableAt (by simp))
    (hFd hp)

/-- Integrability is transported alongside area, so subsequent energy comparisons retain
actual finite integrals. Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449; the explicit
project construction is recorded in
`proof-work/tasks/M64/reports/annular-smooth-cover-chart.md`. -/
theorem scalarInverseCylinderMap_area_integrable (g : RiemannianMetric n M)
    {f : Plane → M} (hf : ContMDiffOn (𝓡 2) (𝓡 n) 1 f scalarAnnulus)
    (hfA : IntegrableOn (m60AreaDensity g f) scalarAnnulus)
    (e : OpenPartialHomeomorph Cover Cover)
    (hsource : e.source = scalarCoverStrip)
    (htarget : e.target = scalarPotentialStrip)
    (hei : ContDiffOn ℝ ∞ e.symm e.target)
    (hdeck : ∀ z ∈ e.source, e (z + (0, 1)) = e z + (0, 1)) :
    IntegrableOn (m60AreaDensity g (f ∘ scalarInverseCylinderMap e))
      scalarCylinderFundamental := by
  let F := scalarInverseCylinderMap e
  have himage : F '' scalarCylinderFundamental = scalarAnnulus :=
    scalarInverseCylinderMap_image_fundamental e hsource htarget hdeck
  have hFd {p : Plane} (hp : p ∈ scalarCylinderFundamental) :
      DifferentiableAt ℝ F p := by
    apply ((scalarInverseCylinderMap_smooth e htarget hei).contDiffAt ?_).differentiableAt
      (by simp)
    exact (isOpen_Ioo.preimage (EuclideanSpace.proj 1).continuous).mem_nhds hp.1
  have hchange := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    scalarCylinderFundamental_measurable
    (fun p hp => (hFd hp).hasFDerivAt.hasFDerivWithinAt)
    (scalarInverseCylinderMap_injOn_fundamental e hsource htarget hdeck)
    (m60AreaDensity g f)
  rw [himage] at hchange
  apply (hchange.mp hfA).congr_fun ?_ scalarCylinderFundamental_measurable
  intro p hp
  have hFp : F p ∈ scalarAnnulus := himage ▸ mem_image_of_mem F hp
  exact (M60.suAreaDensity_comp_plane g
    ((hf.contMDiffAt (scalarAnnulus_isOpen.mem_nhds hFp)).mdifferentiableAt (by simp))
    (hFd hp)).symm

end Area

end PoincareMT.M64Uniformization
