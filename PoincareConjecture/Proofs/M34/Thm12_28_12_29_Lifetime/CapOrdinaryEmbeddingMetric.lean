import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapOrdinaryEmbedding
import PoincareConjecture.Proofs.M34.Standard.CapIsometryScalar
import PoincareConjecture.Proofs.M34.Standard.CapMetricScalingScalar
import PoincareConjecture.Proofs.M13.Completeness

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M34

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T3Space M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  {I : SpacetimeInterval} {F : RicciFlow 3 M I.domain}
  (R : OrdinaryProductRicciGeometry F.metric I)

local notation "G" => ordinaryChapter11Flow (I := I) (F := F) R

theorem ordinaryChapter11CylinderOpenPartialHomeomorph_metric
    {C : GeneralizedSliceCarrier.{u}} {origin scale : ℝ} {K : Set ℝ} {U : Set C.carrier}
    (e : GeneralizedFlowCylinder (G) C origin scale K U) (hU : IsOpen U)
    (s : ℝ) (hs : s ∈ K)
    (ht : origin + s / scale ∈ I.domain) {x : C.carrier} (hx : x ∈ U)
    (v w : TangentSpace (𝓡 3) x) :
    let a := ordinaryChapter11CylinderOpenPartialHomeomorph R e hU s hs ht
    e.pullbackInner s hs x v w =
      (M13.scaleSmoothMetric (F.metric (origin + s / scale)) scale e.scale_pos).inner
        (a x) (mfderiv (𝓡 3) (𝓡 3) a x v) (mfderiv (𝓡 3) (𝓡 3) a x w) := by
  let f := R.product.sliceIdentification ⟨origin + s / scale, ht⟩
  let a := ordinaryChapter11CylinderOpenPartialHomeomorph R e hU s hs ht
  have he : e.forward s hs = f ∘ a := by
    funext y
    exact (f.apply_symm_apply (e.forward s hs y)).symm
  have ha : MDifferentiableAt (𝓡 3) (𝓡 3) a x :=
    (((ordinaryChapter11CylinderOpenPartialHomeomorph_smooth R e hU s hs ht).1 x hx).contMDiffAt
      (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hd : mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) x =
      (mfderiv (𝓡 3) (𝓡 3) f (a x)).comp (mfderiv (𝓡 3) (𝓡 3) a x) := by
    rw [he]
    exact mfderiv_comp x (f.mdifferentiable (by simp) _) ha
  dsimp only
  unfold GeneralizedFlowCylinder.pullbackInner
  rw [hd, congrFun he x, M13.scaleSmoothMetric_inner]
  exact congrArg (fun b : ℝ => scale * b)
    (R.product.sliceMetric_eq ⟨origin + s / scale, ht⟩ (a x)
      (mfderiv (𝓡 3) (𝓡 3) a x v) (mfderiv (𝓡 3) (𝓡 3) a x w))

theorem ordinaryChapter11_scaled_scalarAnalytic (p : (G).point) {Q : ℝ} (hQ : 0 < Q) :
    let g := M13.scaleSmoothMetric (F.metric p.1) Q hQ
    let D := M13.scaleLeviCivitaData (F.connection p.1) Q hQ
    let x := ordinaryChapter11Projection R p
    (D.scalarCurvature x, scalarGradientNorm g D x,
      D.laplacian D.scalarCurvature x + 2 * D.ricciNormSq x) =
    ((G).scalar p / Q,
      scalarGradientNorm ((G).metric p.1) ((G).connection p.1) p.2 / Q ^ (3 / 2 : ℝ),
      (((G).connection p.1).laplacian ((G).connection p.1).scalarCurvature p.2 +
        2 * ((G).connection p.1).ricciNormSq p.2) / Q ^ 2) := by
  let : T25Space M := T3Space.t25Space
  let : T2Space M := T25Space.t2Space
  let t : I.domain := ⟨p.1, ordinaryChapter11Point_time_mem R p⟩
  let f := R.product.sliceIdentification t
  have hf : MetricHomothety (F.metric p.1) ((G).metric p.1) f 1 := by
    exact ordinarySlice_metricHomothety R.product t
  have hbase : f (ordinaryChapter11Projection R p) = p.2 :=
    ordinaryChapter11_identification_projection R t p.2
  have hs := metricIsometry_scalar f hf (F.connection p.1) ((G).connection p.1)
    (ordinaryChapter11Projection R p)
  have hg := metricIsometry_scalarGradient f hf (F.connection p.1) ((G).connection p.1)
    (ordinaryChapter11Projection R p)
  have he := metricIsometry_scalarEvolution f hf (F.connection p.1) ((G).connection p.1)
    (ordinaryChapter11Projection R p)
  rw [hbase] at hs hg he
  dsimp only
  rw [M13.scaleLeviCivitaData_scalarCurvature, M13.scaleSmoothMetric_scalarGradientNorm,
    M13.scaleLeviCivitaData_scalarEvolution, ← hs, ← hg, ← he]
  rfl

theorem ordinaryCap_scaled_metric_complete {n : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] [IsManifold (𝓡 n) ∞ X] [T3Space X]
    (g : RiemannianMetric n X)
    {Q : ℝ} (hQ : 0 < Q) (hcomplete : MetricComplete g) :
    MetricComplete (M13.scaleSmoothMetric g Q hQ) :=
  (M13.homothety_complete_iff g (M13.scaleSmoothMetric g Q hQ)
    (Diffeomorph.refl (𝓡 n) X ∞) Q hQ (M13.identity_metricHomothety g Q hQ)).mpr hcomplete

end PoincareConjecture.M34
