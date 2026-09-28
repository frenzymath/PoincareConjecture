import PoincareConjecture.Proofs.M34.Lemma12_2_InitialMetric.Completeness
import PoincareConjecture.Proofs.M34.Lemma12_2_InitialMetric.Rotations
import PoincareConjecture.Proofs.M34.Lemma12_2_InitialMetric.CylindricalEnd
import PoincareConjecture.Proofs.M34.Lemma12_2_InitialMetric.Curvature











set_option autoImplicit false

namespace PoincareConjecture.M34



noncomputable def standardInitialMetricOfParameter (a : ℝ) (ha : 0 < a)
    (hapi : a ≤ Real.pi / 2) (hn : capProfile a Real.pi = Real.sqrt 2) :
    StandardInitialMetric where
  metric := capRiemannianMetric a ha hapi
  connection := capLeviCivitaData a ha hapi
  complete := capRiemannianMetric_complete ha hapi
  nonnegative_sectional := capNonnegativeSectionalCurvature ha hapi (capLeviCivitaData a ha hapi)
  rotation_invariant := capRiemannianMetric_rotation_invariant a ha hapi
  cylindrical_end := capCylindricalEnd ha hapi hn
  tip_sectional_curvature := capTipSectionalCurvature ha hapi (capLeviCivitaData a ha hapi)



theorem standardInitialMetric_exists : Nonempty StandardInitialMetric := by
  obtain ⟨a, ha, hn⟩ := exists_capProfile_normalized
  exact ⟨standardInitialMetricOfParameter a ha.1 ha.2.le hn⟩

end PoincareConjecture.M34
