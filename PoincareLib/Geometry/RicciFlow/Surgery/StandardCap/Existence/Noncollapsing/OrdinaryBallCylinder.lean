import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Flow.OrdinarySliceMetric
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Noncollapsing.OrdinaryProductCurvature
import PoincareLib.Geometry.Spacetime.Realization.Manifold.OpenSubsetDiffeomorph
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.Spacetime.Realization.Manifold.OpenSubsetDiffeomorph
import PoincareLib.Geometry.RicciFlow.Generalized.Noncollapse.Cylinder.BallTopology
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Curvature.Calculus.Fields.ConnectionScalar
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Curvature.Calculus.Fields.FixedExtension
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Curvature.Calculus.Identities.CurvatureAlgebra
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Curvature.Calculus.Identities.CurvatureSymmetries
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Curvature.Calculus.Tensors.RiemannRegularity
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Curvature.Estimates.QuadraticRicci
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Generalized.Noncollapse.Cylinder.BallTopology
import PoincareLib.Geometry.RicciFlow.Generalized.Noncollapse.Provider

/-!
# The actual ordinary ball cylinder for M15

Time restriction and open spatial restriction of the retained compatible
product cylinder give the genuine cylinder based on every point of the
terminal ball. Its curvature estimate holds on the full closed window.
Source: Morgan-Tian Proposition 12.13, pp. 304-306; Theorem 8.1, p. 169.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M34

/-- The nondegenerate closed backward time window of a positive-radius
ordinary ball (Theorem 8.1, p. 169). -/
def ordinaryBallInterval (T r : ℝ) (hr : 0 < r) : SpacetimeInterval where
  domain := Icc (T - r ^ 2) T
  ordConnected := ordConnected_Icc
  nontrivial := ⟨T - r ^ 2, ⟨le_rfl, sub_le_self _ (sq_nonneg r)⟩,
    T, ⟨sub_le_self _ (sq_nonneg r), le_rfl⟩,
    ne_of_lt (sub_lt_self T (sq_pos_of_pos hr))⟩

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- The actual open terminal ball as a smooth source carrier
(Proposition 12.13, pp. 304-306). -/
noncomputable def ordinaryBallSource [T2Space M]
    (g : RiemannianMetric n M) (p : M) (r : ℝ) :
    TopologicalSpace.Opens M := ⟨g.ball p r, M04.initial_ball_isOpen g p r⟩

variable [T3Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

set_option backward.isDefEq.respectTransparency false in
/-- Restriction of the actual retained product gives the full based ball
cylinder required by Theorem 8.1 (Proposition 12.13, pp. 304-306). -/
theorem ordinaryProduct_ballCylinder {I : SpacetimeInterval} {F : RicciFlow n M I.domain}
    (R : OrdinaryProductRicciGeometry F.metric I)
    (hRicci : IntrinsicGeneralizedRicciEquation R.leafwiseConnection)
    {T r : ℝ} (hT : T ∈ I.domain) (p : M) (hr : 0 < r)
    (C : MetricHomothetyCalculus (F.metric T) (R.product.slices T).metricOnPoints
      (R.product.sliceIdentification ⟨T, hT⟩) 1)
    (hI : Icc (T - r ^ 2) T ⊆ I.domain)
    (hcurv : ∀ s ∈ Icc (T - r ^ 2) T, ∀ q ∈ (F.metric T).ball p r,
      (F.connection s).curvatureTensorNorm q ≤ r⁻¹ ^ 2) :
    Nonempty (M15ActualBallCylinder (ordinaryProductLGeometry R hRicci) T
      (R.product.sliceIdentification ⟨T, hT⟩ p) r (ordinaryBallInterval T r hr)
      (ordinaryBallSource (F.metric T) p r)) := by
  let K := ordinaryBallInterval T r hr
  let U := ordinaryBallSource (F.metric T) p r
  let iota := R.product.sliceIdentification ⟨T, hT⟩
  have hK : K.domain ⊆ I.domain := hI
  obtain ⟨eT, heT⟩ := R.product.compatible.cylinder_time_restrict
    M I K hK R.product.productCylinder
  obtain ⟨eB, heB⟩ := R.product.compatible.cylinder_open_restrict M K eT U
  obtain ⟨gB⟩ := R.product.compatible.cylinder_metric U K eB
  let f : U → (R.product.slices T).Point := iota ∘ Subtype.val
  have hf : ContMDiff (𝓡 n) (𝓡 n) ∞ f :=
    iota.contMDiff.comp contMDiff_subtype_val
  refine ⟨{
    radius_pos := hr
    interval_domain := rfl
    base_mem := ⟨sub_le_self _ (sq_nonneg r), le_rfl⟩
    embedding := eB
    metric := gB
    source_map := f
    source_map_embedding := iota.toHomeomorph.isEmbedding.comp .subtypeVal
    source_map_range := ?_
    based := ?_
    source_map_smooth := hf.contMDiffOn
    source_map_differential_injective := ?_
    curvature_bound := ?_
  }⟩
  · have he : range f = iota '' (F.metric T).ball p r := by
      ext y
      constructor
      · rintro ⟨z, rfl⟩
        exact ⟨z.val, z.property, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        exact ⟨⟨z, hz⟩, rfl⟩
    exact he.trans (ordinarySlice_ball R.product ⟨T, hT⟩ C p r)
  · intro c
    rw [heB, heT, R.product.productCylinder_eq]
    exact (R.product.sliceIdentification_eq ⟨T, hT⟩ c.val).symm
  · intro c
    change Function.Injective (mfderiv (𝓡 n) (𝓡 n) f c)
    have hd := mfderiv_comp c (iota.contMDiff _ |>.mdifferentiableAt (by simp))
      (contMDiff_subtype_val (n := ∞) c |>.mdifferentiableAt (by simp))
    change mfderiv (𝓡 n) (𝓡 n) f c = _ at hd
    rw [hd]
    exact (iota.mfderivToContinuousLinearEquiv (by simp) c.val).injective.comp
      (Proofs.M11.openSubset_differential_injective U c)
  · intro s c
    change horizontalCurvatureNorm R.leafwiseConnection (eB.toSpacetime (s, c)) ≤ r⁻¹ ^ 2
    rw [heB, heT, ← ordinaryProduct_curvatureNorm_eq R F.connection]
    exact hcurv s.val s.property c.val c.property

end PoincareMT.M34
