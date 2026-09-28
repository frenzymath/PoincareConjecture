import PoincareConjecture.Proofs.M34.Standard.CapIsometryCertificate
import PoincareConjecture.Proofs.M34.Standard.CapIsometryNeck

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.CapCertificate

variable {M X : Type u} [TopologicalSpace M] [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
  [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ X]
  [MeasurableSpace M] [MeasurableSpace X] [BorelSpace M] [BorelSpace X]
  [T3Space M] [T3Space X]
  {g : RiemannianMetric 3 M} {h : RiemannianMetric 3 X}

theorem exists_isometric_image_cap (N : CapCertificate g)
    (f : Diffeomorph (𝓡 3) (𝓡 3) M X ∞) (hf : MetricHomothety g h f 1)
    (D : LeviCivitaData h) :
    ∃ H : CapCertificate h, H.epsilon = N.epsilon ∧ H.cap_constant = N.cap_constant ∧
      H.connection = D ∧ H.core = f '' N.core ∧ H.carrier = f '' N.carrier := by
  let : T25Space X := T3Space.t25Space
  let : T2Space X := T25Space.t2Space
  obtain ⟨Eend, he, _, _, hD, hcarrier, _, hregion⟩ :=
    N.end_neck.exists_isometric_image f hf D
  obtain ⟨Eboundary, he', _, _, hD', hcarrier', hsphere, _⟩ :=
    N.boundary_neck.exists_isometric_image f hf D
  apply N.exists_isometric_image_cap_of_necks f hf D Eend Eboundary
    (he.trans N.end_neck_epsilon) (he'.trans N.boundary_neck_epsilon)
    hD hD' hcarrier hcarrier'
  · rwa [← N.boundary_eq_neck_sphere] at hsphere
  · exact hregion _ _ (by rw [N.end_neck_epsilon]) (by
      rw [N.end_neck_epsilon]
      have hi := inv_pos.mpr N.epsilon_pos
      linarith)

end PoincareConjecture.CapCertificate
