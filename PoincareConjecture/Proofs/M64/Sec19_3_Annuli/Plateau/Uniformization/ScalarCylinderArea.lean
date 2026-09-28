import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarInverseFibers
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarOpenCylinder
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerAnnularCap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Cover" => ℝ × ℝ

def scalarCylinderFundamental : Set Plane :=
  {p | p 1 ∈ Ioo (0 : ℝ) 1 ∧ p 0 ∈ Ico (0 : ℝ) curvePeriod}

def scalarInverseCylinderMap (e : OpenPartialHomeomorph Cover Cover) : Plane → Plane :=
  scalarInverseCoverMap e ∘ scalarCylinderCoordinate

private theorem period_pos : 0 < curvePeriod := by
  unfold curvePeriod
  positivity

theorem scalarCylinderFundamental_measurable : MeasurableSet scalarCylinderFundamental :=
  (measurableSet_Ioo.preimage (EuclideanSpace.proj 1).continuous.measurable).inter
    (measurableSet_Ico.preimage (EuclideanSpace.proj 0).continuous.measurable)

theorem scalarCylinderCoordinate_mem_fundamental {p : Plane}
    (hp : p ∈ scalarCylinderFundamental) :
    scalarCylinderCoordinate p ∈ scalarPotentialStrip ∩ {y | y.2 ∈ Ico (0 : ℝ) 1} := by
  refine ⟨hp.1, ?_, ?_⟩
  · exact mul_nonneg (inv_nonneg.mpr period_pos.le) hp.2.1
  · change curvePeriod⁻¹ * p 0 < 1
    rw [← inv_mul_cancel₀ period_pos.ne']
    exact mul_lt_mul_of_pos_left hp.2.2 (inv_pos.mpr period_pos)

theorem scalarInverseCylinderMap_smooth (e : OpenPartialHomeomorph Cover Cover)
    (htarget : e.target = scalarPotentialStrip)
    (hei : ContDiffOn ℝ ∞ e.symm e.target) :
    ContDiffOn ℝ ∞ (scalarInverseCylinderMap e) {p | p 1 ∈ Ioo (0 : ℝ) 1} := by
  intro p hp
  have hp' : scalarCylinderCoordinate p ∈ e.target := htarget ▸ hp
  exact (((scalarInverseCoverMap_smooth e hei).contDiffAt
    (e.open_target.mem_nhds hp')).comp p
    scalarCylinderCoordinate.contDiff.contDiffAt).contDiffWithinAt

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

end PoincareConjecture.M64Uniformization
