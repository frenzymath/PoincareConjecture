import PoincareConjecture.Proofs.M60.Mathlib.MetricPullbackForm
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.SphereTangent










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff

noncomputable section

namespace PoincareConjecture

private noncomputable def sphereAmbientMetric : RiemannianMetric 3 LoopAmbient :=
  { riemannianMetricVectorSpace LoopAmbient with
    contMDiff := (riemannianMetricVectorSpace LoopAmbient).contMDiff.of_le le_top }

local instance (p : UnitTwoSphere) : NormedAddCommGroup (TangentSpace (𝓡 2) p) :=
  inferInstanceAs (NormedAddCommGroup LoopPlane)

local instance (p : UnitTwoSphere) : InnerProductSpace ℝ (TangentSpace (𝓡 2) p) :=
  inferInstanceAs (InnerProductSpace ℝ LoopPlane)



noncomputable def m60RoundSphereMetric : RiemannianMetric 2 UnitTwoSphere where
  inner := M60.metricPullbackForm (n := 2) sphereAmbientMetric (fun p : UnitTwoSphere => p.1)
  symm p v w := by
    change m60RoundSphereInner p v w = m60RoundSphereInner p w v
    rw [m60RoundSphereInner_eq_inner, m60RoundSphereInner_eq_inner]
    exact real_inner_comm _ _
  pos p v hv := by
    change 0 < m60RoundSphereInner p v v
    rw [m60RoundSphereInner_eq_inner]
    exact real_inner_self_pos.mpr hv
  isVonNBounded p := by
    change Bornology.IsVonNBounded ℝ {v : TangentSpace (𝓡 2) p |
      m60RoundSphereInner p v v < 1}
    simp_rw [m60RoundSphereInner_eq_inner]
    exact (riemannianMetricVectorSpace LoopPlane).isVonNBounded 0
  contMDiff p := by
    let : Fact (Module.finrank ℝ LoopAmbient = 2 + 1) := ⟨by simp [LoopAmbient]⟩
    exact M60.metricPullbackForm_contMDiffAt sphereAmbientMetric
      ((contMDiff_coe_sphere (n := 2) (m := ∞)) p)



theorem m60RoundSphereMetric_inner (p : UnitTwoSphere)
    (v w : TangentSpace (𝓡 2) p) :
    m60RoundSphereMetric.inner p v w = m60RoundSphereInner p v w := rfl

end PoincareConjecture

end
