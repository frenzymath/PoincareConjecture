import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.Functionals
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Measure.Green.ChangeOfVariables
import Mathlib.Geometry.Manifold.Diffeomorph

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture

theorem m60SphereMetric_volume_singleton (g : RiemannianMetric 2 UnitTwoSphere)
    (p : UnitTwoSphere) : g.volumeMeasure {p} = 0 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : UnitTwoSphere → Type) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle LoopPlane
      (TangentSpace (𝓡 2) : UnitTwoSphere → Type) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace UnitTwoSphere := EMetricSpace.ofRiemannianMetric (𝓡 2) UnitTwoSphere
  let : NullSingletonClass (Measure.hausdorffMeasure (2 : ℝ) : Measure UnitTwoSphere) :=
    Measure.nullSingletonClass_hausdorff UnitTwoSphere (by norm_num)
  change (Measure.euclideanHausdorffMeasure 2 : Measure UnitTwoSphere) {p} = 0
  rw [Measure.euclideanHausdorffMeasure_def]
  simp

theorem m60SphereMetric_pullbackVolumeDensity (g : RiemannianMetric 2 UnitTwoSphere)
    (F : LoopPlane → UnitTwoSphere) (z : LoopPlane) :
    g.pullbackVolumeDensity F z = m60AreaDensity g F z := by
  unfold RiemannianMetric.pullbackVolumeDensity m60AreaDensity
  rw [max_eq_right (m60AreaGram_det_nonneg g F z)]
  rfl

theorem m60SphereMetric_area_diffeomorph (g : RiemannianMetric 2 UnitTwoSphere)
    (phi : UnitTwoSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ UnitTwoSphere) :
    m60SphereArea g phi = g.volumeMeasure.real univ := by
  let e : OpenPartialHomeomorph LoopPlane UnitTwoSphere :=
    m60SphereChart.symm.trans phi.toHomeomorph.toOpenPartialHomeomorph
  have hsource : e.source = univ := by
    simp [e, m60SphereChart]
  have htarget : e.target = {phi m60SpherePole}ᶜ := by
    ext p
    simp only [e, OpenPartialHomeomorph.trans_target,
      Homeomorph.toOpenPartialHomeomorph_target, OpenPartialHomeomorph.symm_target,
      mem_inter_iff, mem_univ, true_and, mem_preimage, mem_compl_iff, mem_singleton_iff]
    simp only [m60SphereChart, stereographic'_source, mem_compl_iff, mem_singleton_iff]
    exact not_congr phi.toEquiv.symm_apply_eq
  have he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source :=
    (phi.contMDiff.comp m60SphereParameter_contMDiff).contMDiffOn
  have hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target := by
    change ContMDiffOn (𝓡 2) (𝓡 2) ∞ (m60SphereChart ∘ phi.symm) e.target
    have hc : ContMDiffOn (𝓡 2) (𝓡 2) ∞ m60SphereChart m60SphereChart.source := by
      rw [m60SphereChart_eq_chartAt]
      exact contMDiffOn_chart
    refine hc.comp phi.symm.contMDiff.contMDiffOn ?_
    intro p hp
    have ht : e.target = phi.symm ⁻¹' m60SphereChart.source := by
      simp [e]
    exact ht ▸ hp
  have hi := g.integral_target_eq_integral_pullback_density e he hei
    (f := fun _ => (1 : ℝ)) continuousOn_const
  have hae : ∀ᵐ p ∂g.volumeMeasure, p ∈ e.target := by
    rw [ae_iff, htarget]
    simpa only [not_not, mem_compl_iff, ofPred_mem_eq] using
      m60SphereMetric_volume_singleton g (phi m60SpherePole)
  rw [← integral_eq_setIntegral hae (fun _ => (1 : ℝ)), hsource, setIntegral_univ] at hi
  simp only [integral_const, smul_eq_mul, mul_one, one_mul] at hi
  rw [hi]
  unfold m60SphereArea m60SphereAreaDensity
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z =>
    (m60SphereMetric_pullbackVolumeDensity g (phi ∘ m60SphereParameter) z).symm

theorem m60SphereMetric_area_diffeomorph_eq (g : RiemannianMetric 2 UnitTwoSphere)
    (phi : UnitTwoSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ UnitTwoSphere) :
    m60SphereArea g phi = m60SphereArea g id := by
  rw [m60SphereMetric_area_diffeomorph g phi]
  exact (m60SphereMetric_area_diffeomorph g (Diffeomorph.refl (𝓡 2) UnitTwoSphere ∞)).symm

end PoincareConjecture
