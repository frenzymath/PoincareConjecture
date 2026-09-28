import PoincareConjecture.Proofs.M15.Thm8_10_OrdinaryProduct
import PoincareConjecture.Definitions.M15Noncollapsing
import PoincareConjecture.Statements.M13Rescaling
import PoincareConjecture.Proofs.M11.OpenSubsetDiffeomorph
import PoincareConjecture.Proofs.M04.ShiCarrier

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M15

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T3Space M] [MeasurableSpace M] [BorelSpace M] {I : SpacetimeInterval}

theorem ordinaryProduct_slice_calculus
    (hM13 : GeneralizedParabolicRescalingTheory.{u} n)
    (F : RicciFlow n M I.domain)
    (P : OrdinaryProductRicciGeometry F.metric I) (t : I.domain) :
    MetricHomothetyCalculus (F.metric t.val)
      ((ordinaryProductTransport F P).slices t.val).metricOnPoints
      (P.product.sliceIdentification t) 1 := by
  apply hM13.metric_homothety M ((ordinaryProductTransport F P).slices t.val).Point
    (F.metric t.val) ((ordinaryProductTransport F P).slices t.val).metricOnPoints
    (P.product.sliceIdentification t) 1 zero_lt_one
  intro x v w
  simpa only [one_mul] using! P.product.sliceMetric_eq t x v w

variable [SecondCountableTopology M]

theorem ordinaryProduct_actualBallCylinder
    (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (hM13 : GeneralizedParabolicRescalingTheory.{u} n)
    (F : RicciFlow n M I.domain)
    (P : OrdinaryProductRicciGeometry F.metric I)
    (T : I.domain) (p : M) {r : ℝ} (hr : 0 < r)
    (K : SpacetimeInterval)
    (hK : K.domain = Icc (T.val - r ^ 2) T.val)
    (hKI : K.domain ⊆ I.domain)
    (hcurv : ∀ s ∈ K.domain, ∀ q ∈ (F.metric T.val).ball p r,
      (F.connection s).curvatureTensorNorm q ≤ r⁻¹ ^ 2) :
    ∃ U : TopologicalSpace.Opens M,
      Nonempty (M15ActualBallCylinder (ordinaryProductTransport F P) T.val
        (P.product.sliceIdentification T p) r K U) := by
  let G := ordinaryProductTransport F P
  let U : TopologicalSpace.Opens M :=
    ⟨(F.metric T.val).ball p r, M04.initial_ball_isOpen (F.metric T.val) p r⟩
  obtain ⟨e1, he1⟩ := P.product.compatible.cylinder_time_restrict M I K hKI
    P.product.productCylinder
  obtain ⟨e2, he2⟩ := P.product.compatible.cylinder_open_restrict M K e1 U
  obtain ⟨g⟩ := P.product.compatible.cylinder_metric U K e2
  have he (s : (G.timeIntervals.interval K).Point) (q : U) :
      e2.toSpacetime (s, q) = P.product.productCylinder.toSpacetime
        (⟨s.val, hKI s.property⟩, q.val) := by
    rw [he2, he1]
    rfl
  let f : U → (G.slices T.val).Point := P.product.sliceIdentification T ∘ Subtype.val
  have hf : ContMDiff (𝓡 n) (𝓡 n) ∞ f :=
    (P.product.sliceIdentification T).contMDiff.comp contMDiff_subtype_val
  have hbase : T.val ∈ K.domain := by
    rw [hK]
    exact ⟨sub_le_self _ (sq_nonneg r), le_rfl⟩
  refine ⟨U, ⟨{
    radius_pos := hr
    interval_domain := hK
    base_mem := hbase
    embedding := e2
    metric := g
    source_map := f
    source_map_embedding :=
      (P.product.sliceIdentification T).toHomeomorph.isEmbedding.comp .subtypeVal
    source_map_range := ?_
    based := ?_
    source_map_smooth := hf.contMDiffOn
    source_map_differential_injective := ?_
    curvature_bound := ?_
  }⟩⟩
  · have hrange : range f = P.product.sliceIdentification T '' (F.metric T.val).ball p r := by
      ext y
      constructor
      · rintro ⟨q, rfl⟩
        exact ⟨q.val, q.property, rfl⟩
      · rintro ⟨q, hq, rfl⟩
        exact ⟨⟨q, hq⟩, rfl⟩
    rw [hrange]
    simpa using! (ordinaryProduct_slice_calculus hM13 F P T).ball_image p r
  · intro q
    change e2.toSpacetime (⟨T.val, hbase⟩, q) =
      (P.product.sliceIdentification T q.val).val
    rw [he, P.product.productCylinder_eq, P.product.sliceIdentification_eq]
  · intro q
    have hd := mfderiv_comp q
      ((P.product.sliceIdentification T).contMDiff.mdifferentiableAt (by simp))
      ((contMDiff_subtype_val (n := ∞)).mdifferentiableAt (by simp))
    change mfderiv (𝓡 n) (𝓡 n) f q = _ at hd
    rw [hd]
    exact ((P.product.sliceIdentification T).mfderivToContinuousLinearEquiv
      (by simp) q.val).injective.comp (M11.openSubset_differential_injective U q)
  · intro s q
    rw [he]
    have hc := (ordinaryProduct_moving_calculus hM12 F P).curvature_norm_eq
      ⟨s.val, hKI s.property⟩ q.val
    exact hc.symm.le.trans (hcurv s.val s.property q.val q.property)

end PoincareConjecture.Proofs.M15
