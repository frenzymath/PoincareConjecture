import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.InitialMetric.Completeness
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.InitialMetric.Rotations
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.InitialMetric.CylindricalEnd
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.InitialMetric.Curvature

/-!
# Existence of a standard initial metric

Morgan-Tian Definition 12.1 and Lemma 12.2, printed pp. 293-295. The
normalized smooth concave profile gives a complete rotational metric
with a round tip, nonnegative sectional curvature, and an exact radius
sqrt(2) cylindrical end with a smooth boundary collar. All fields below
are proved against the frozen StandardInitialMetric structure.
-/

set_option autoImplicit false

namespace PoincareMT.M34

/-- The complete standard initial metric associated to a normalized
positive cutoff parameter (Definition 12.1 and Lemma 12.2, pp. 293-295). -/
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

/-- A standard initial metric exists, with every geometric field
constructed rather than supplied (Morgan-Tian Lemma 12.2, pp. 294-295). -/
theorem standardInitialMetric_exists : Nonempty StandardInitialMetric := by
  obtain ⟨a, ha, hn⟩ := exists_capProfile_normalized
  exact ⟨standardInitialMetricOfParameter a ha.1 ha.2.le hn⟩

end PoincareMT.M34
