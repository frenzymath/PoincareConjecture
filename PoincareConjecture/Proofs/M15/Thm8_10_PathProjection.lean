import PoincareConjecture.Proofs.M15.Thm8_10_OrdinaryProduct
import PoincareConjecture.Proofs.M15.Lemma8_7_LiftedVelocity
import PoincareConjecture.Definitions.Ch06.LGeometry

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M15

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {I : SpacetimeInterval}

theorem ordinaryProduct_backwardIntegrand_eq
    (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (F : RicciFlow n M I.domain)
    (P : OrdinaryProductRicciGeometry F.metric I)
    {T a b : ℝ} {x y : (ordinaryProductTransport F P).Point}
    (p : M14BackwardPath (ordinaryProductTransport F P) T a b x y)
    {s : ℝ} (hs : s ∈ Ioo a b) :
    backwardLIntegrand F T (fun t => (p.curve t).2) s =
      M14BackwardLIntegrand (ordinaryProductTransport F P) p s := by
  let G := ordinaryProductTransport F P
  let L : ℝ → (P.product.timeIntervals.interval I).Point × M :=
    P.product.productIdentification.symm ∘ p.curve
  have hid : ∀ q : G.Point, P.product.productIdentification.symm q = q := by
    intro q
    have h := P.product.productIdentification_eq (P.product.productIdentification.symm q)
    rw [P.product.productIdentification.apply_symm_apply] at h
    exact h.symm
  have hL : L = p.curve := funext fun t => hid (p.curve t)
  have he : P.product.productCylinder.toSpacetime ∘ L = p.curve := by
    funext t
    exact (P.product.productCylinder_eq (L t)).trans (congrFun hL t)
  have hreg : ContMDiffOn 𝓘(ℝ) (spacetimeModel n) 1 L (Ioo a b) :=
    (P.product.productIdentification.symm.contMDiff.of_le (by simp)).comp_contMDiffOn
      p.curve_regular
  have hnh : Ioo a b ∈ 𝓝 s := isOpen_Ioo.mem_nhds hs
  have hproj := compatibleCylinder_horizontalDerivative_lift P.product.productCylinder
    (ordinaryProductCylinderMetric F P) L
    ((hreg s hs).mdifferentiableWithinAt (by simp))
    (isOpen_Ioo.uniqueDiffWithinAt hs)
  rw [he, mfderivWithin_of_mem_nhds hnh,
    mfderivWithin_of_mem_nhds hnh] at hproj
  have htime : G.spacetime.horizontalProjection (p.curve s)
      (G.spacetime.timeVector (p.curve s)) = 0 := by
    apply Subtype.ext
    simp only [G.spacetime.horizontalProjection_eq,
      G.spacetime.timeVector_normalized, one_smul, sub_self]
    rfl
  have hclock : (p.curve s).1.val = T - s := p.curve_time s (Ioo_subset_Icc_self hs)
  have hscalar := (ordinaryProduct_moving_calculus hM12 F P).scalar_eq
    (p.curve s).1 (p.curve s).2
  change (F.connection (p.curve s).1.val).scalarCurvature (p.curve s).2 =
    horizontalScalarCurvature G.leafwise
      (P.product.productCylinder.toSpacetime (p.curve s)) at hscalar
  rw [P.product.productCylinder_eq, hclock] at hscalar
  have hmetric := (ordinaryProductCylinderMetric F P).metric_eq
    (L s).1 (L s).2
    (curveVelocity (n := n) (fun t => (L t).2) s)
    (curveVelocity (n := n) (fun t => (L t).2) s)
  unfold curveVelocity at hmetric
  rw [hproj] at hmetric
  erw [hL, P.product.productCylinder_eq] at hmetric
  erw [p.derivative_eq s hs, map_add, map_neg, htime, neg_zero,
    G.spacetime.horizontalProjection_identity, zero_add] at hmetric
  change (F.metric (p.curve s).1.val).inner _ _ _ = _ at hmetric
  rw [hclock] at hmetric
  unfold backwardLIntegrand M14BackwardLIntegrand M14RawLIntegrand
  erw [hscalar, hmetric]
  rfl

theorem ordinaryProduct_backwardPath_projection
    (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (F : RicciFlow n M I.domain)
    (P : OrdinaryProductRicciGeometry F.metric I)
    {T a b : ℝ} (hT : T ∈ I.domain)
    {x y : (ordinaryProductTransport F P).Point}
    (p : M14BackwardPath (ordinaryProductTransport F P) T a b x y) :
    ∃ q : BackwardTimePath F T a b,
      q.curve = (fun t => (p.curve t).2) := by
  refine ⟨{
    curve := fun t => (p.curve t).2
    nonnegative := p.tau_nonneg
    ordered := p.tau_lt
    terminal_mem := hT
    time_mem := ?_
    continuous := (ordinaryProduct_spatial_smooth F P).continuous.comp_continuousOn
      p.curve_continuous
    regular := (ordinaryProduct_spatial_smooth F P).of_le (by simp)
      |>.comp_contMDiffOn p.curve_regular
    l_integrable := ?_
  }, rfl⟩
  · intro s hs
    have h := (p.curve s).1.property
    change (p.curve s).1.val ∈ I.domain at h
    have ht : (p.curve s).1.val = T - s := p.curve_time s hs
    rwa [ht] at h
  · apply p.action_integrable.congr_uIoo
    intro s hs
    have hi : s ∈ Ioo a b := by simpa only [uIoo_of_le p.tau_lt.le] using hs
    exact (ordinaryProduct_backwardIntegrand_eq hM12 F P p hi).symm

end PoincareConjecture.Proofs.M15
