import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.OrdinaryGeometry
import PoincareConjecture.Proofs.M34.Standard.NonnegativePinching
import PoincareConjecture.Proofs.M13.PinchingIsometry
import PoincareConjecture.Proofs.M04.PointwiseFlatness
import PoincareConjecture.Definitions.M28BoundedDistance











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M34

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T3Space M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  {I : SpacetimeInterval} {F : RicciFlow 3 M I.domain}



theorem ordinaryChapter11_nonnegative
    (R : OrdinaryProductRicciGeometry F.metric I)
    (C : ∀ t : I.domain,
      MetricHomothetyCalculus (F.metric t.val) (R.product.slices t.val).metricOnPoints
        (R.product.sliceIdentification t) 1)
    (_hI : I.domain ⊆ Ici 0)
    (hsec : ∀ t ∈ I.domain, (F.connection t).NonnegativeSectionalCurvature) :
    generalizedNonnegativeCurvature (ordinaryChapter11Flow R) := by
  have hquant (t : ℝ) (ht : t ∈ I.domain)
      (x : ((ordinaryChapter11Flow R).slice t).carrier) :
      0 ≤ (ordinaryChapter11Flow R).scalar ⟨t, x⟩ ∧
        ((ordinaryChapter11Flow R).connection t).negativeCurvaturePart x = 0 := by
    constructor
    · rw [ordinaryChapter11_scalar_eq R C]
      exact M04.nonneg_scalar_of_nonnegativeSectionalAt (F.connection t) x.val.2
        (hsec t ht x.val.2)
    · have h := Proofs.M13.negativeCurvaturePart_eq_one (C ⟨t, ht⟩)
        (ordinarySlice_metricHomothety R.product ⟨t, ht⟩) (F.connection t)
        (R.leafwiseConnection.sliceConnection t) x.val.2
      rw [ordinaryChapter11_identification_projection R ⟨t, ht⟩ x] at h
      exact h.trans (negativeCurvaturePart_eq_zero_of_nonnegativeSectionalAt
        (F.connection t) x.val.2 (hsec t ht x.val.2))
  refine ⟨hquant, ?_⟩
  intro t ht x
  obtain ⟨hscalar, hneg⟩ := hquant t ht x
  refine ⟨by linarith, ?_⟩
  intro hpos
  rw [hneg] at hpos
  exact (lt_irrefl 0 hpos).elim

end PoincareConjecture.M34
