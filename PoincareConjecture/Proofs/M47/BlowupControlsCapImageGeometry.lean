import PoincareConjecture.Proofs.M47.BlowupControlsCapGeometricMargins
import PoincareConjecture.Proofs.M34.Standard.CapIntrinsicDiameter
import PoincareConjecture.Proofs.M34.Standard.LocalCalibratedImageVolume









set_option autoImplicit false

open Set
open scoped Manifold ContDiff ENNReal

universe v

namespace PoincareConjecture.M47

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] [SecondCountableTopology M]




theorem exists_cap_image_geometric_tolerance {g : RiemannianMetric 3 M}
    (N : CapCertificate g) :
    ∃ Lambda : ℝ, 1 < Lambda ∧ ∃ nu : ℝ, 0 < nu ∧
      ∀ (X : Type v) [TopologicalSpace X]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [IsManifold (𝓡 3) ∞ X]
        [MeasurableSpace X] [BorelSpace X] [T3Space X],
      ∀ (h : RiemannianMetric 3 X) (D : LeviCivitaData h)
        (e : OpenPartialHomeomorph M X),
        ContMDiffOn (𝓡 3) (𝓡 3) 1 e e.source → N.carrier ⊆ e.source →
        (∀ x ∈ e.source, ∀ v : TangentSpace (𝓡 3) x,
          h.tangentNorm (e x) (mfderiv (𝓡 3) (𝓡 3) e x v) ≤
            Lambda * g.tangentNorm x v) →
        (∀ x ∈ N.carrier,
          |D.scalarCurvature (e x) - N.connection.scalarCurvature x| ≤ nu) →
        0 < scalarCurvatureSupOn h D (e '' N.carrier) ∧
        intrinsicDiameter h (e '' N.carrier) <
          ENNReal.ofReal (N.cap_constant *
            scalarCurvatureSupOn h D (e '' N.carrier) ^ (-1 / 2 : ℝ)) ∧
        calibratedMetricVolume h (e '' N.carrier) <
          ENNReal.ofReal N.cap_constant *
            ENNReal.ofReal (scalarCurvatureSupOn h D (e '' N.carrier) ^ (-3 / 2 : ℝ)) := by
  obtain ⟨Lambda, hLambda, nu, hnu, hmargin⟩ := exists_cap_geometric_margin N
  have hLpos : 0 < Lambda := zero_lt_one.trans hLambda
  refine ⟨Lambda, hLambda, nu, hnu, ?_⟩
  intro X _ _ _ _ _ _ h D e hf hsource hmetric hscalar
  have hsup := cap_image_scalarSup_close N h D e hscalar
  obtain ⟨hpositive, hdiameter, hvolume⟩ := hmargin _ hsup
  refine ⟨hpositive, ?_, ?_⟩
  · exact (g.intrinsicDiameter_image_le_mul_of_isOpen h e N.carrier_open
      (hf.mono hsource) hLpos (fun x hx v => hmetric x (hsource hx) v)).trans_lt hdiameter
  · exact (M34.calibratedMetricVolume_image_le_of_local_tangentNorm_le
      g h e hf hLpos hmetric N.carrier_open.measurableSet hsource).trans_lt hvolume

end PoincareConjecture.M47
