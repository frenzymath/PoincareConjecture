import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.LocalIsometryInvariants
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularLevel.OpenInclusion
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.OpenEmbedding
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Splitting.MaximumPrinciple.RicciNullity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace VectorField
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M47

open Poincare.Geometry.Manifold.RegularLevel RicciFlow.Splitting

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} (D : LeviCivitaData g) (U : Opens M)
  {h : RiemannianMetric n U} (E : LeviCivitaData h)
  (hmetric : ∀ (x : U) (v w : TangentSpace (𝓡 n) x),
    h.inner x v w = g.inner x.val v w)

include hmetric in

theorem terminalCurvature_open_inclusion_readouts (x : U) :
    E.scalarCurvature x = D.scalarCurvature x.val ∧
    (∀ v w z a, E.curvatureTensor x v w z a = D.curvatureTensor x.val v w z a) ∧
    (∀ v w, E.ricci x v w = D.ricci x.val v w) ∧
    ricciKernel E x = ricciKernel D x.val ∧
    ricciNullity E x = ricciNullity D x.val := by
  have hm (y : U) (_ : y ∈ (univ : Set U)) (v w : TangentSpace (𝓡 n) y) :
      h.inner y v w = g.inner y.val
        (mfderiv (𝓡 n) (𝓡 n) (Subtype.val : U → M) y v)
        (mfderiv (𝓡 n) (𝓡 n) (Subtype.val : U → M) y w) := by
    simpa only [mfderiv_opens_subtypeVal_apply] using hmetric y v w
  have hr (v w : TangentSpace (𝓡 n) x) : E.ricci x v w = D.ricci x.val v w := by
    simpa only [mfderiv_opens_subtypeVal_apply] using
      E.ricci_eq_of_local_isometry D isOpen_univ contMDiff_subtype_val.contMDiffOn
        hm (mem_univ x) v w
  have hk : ricciKernel E x = ricciKernel D x.val := by
    ext v
    simp only [mem_ricciKernel, hr]
    rfl
  refine ⟨E.scalarCurvature_eq_of_local_isometry D isOpen_univ
    contMDiff_subtype_val.contMDiffOn hm (mem_univ x), ?_, hr, hk, ?_⟩
  · intro v w z a
    simpa only [mfderiv_opens_subtypeVal_apply] using
      E.curvatureTensor_eq_of_local_isometry D isOpen_univ
        contMDiff_subtype_val.contMDiffOn hm (mem_univ x) v w z a
  · unfold ricciNullity
    rw [hk]
    rfl

omit [IsManifold (𝓡 n) ∞ M] in

theorem terminalCurvature_open_mpullback
    (V : (x : M) → TangentSpace (𝓡 n) x) (x : U) :
    mpullback (𝓡 n) (𝓡 n) (Subtype.val : U → M) V x = V x.val := by
  unfold mpullback
  rw [mfderiv_opens_subtypeVal]
  change (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))).inverse (V x.val) = _
  rw [ContinuousLinearMap.inverse_id]
  rfl

include hmetric in

theorem terminalCurvature_open_connection
    (V : (x : M) → TangentSpace (𝓡 n) x) (x : U)
    (hV : MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) (T% V) x.val)
    (v : TangentSpace (𝓡 n) x) :
    E.connection (mpullback (𝓡 n) (𝓡 n) (Subtype.val : U → M) V) x v =
      D.connection V x.val v := by
  have hm : ∀ᶠ y : U in 𝓝 x, ∀ a b : TangentSpace (𝓡 n) y,
      h.inner y a b = g.inner y.val
        (mfderiv (𝓡 n) (𝓡 n) (Subtype.val : U → M) y a)
        (mfderiv (𝓡 n) (𝓡 n) (Subtype.val : U → M) y b) :=
    Eventually.of_forall fun y a b => by
      simpa only [mfderiv_opens_subtypeVal_apply] using hmetric y a b
  have hi : ∀ᶠ y : U in 𝓝 x,
      (mfderiv (𝓡 n) (𝓡 n) (Subtype.val : U → M) y).IsInvertible :=
    Eventually.of_forall fun y => by
      rw [mfderiv_opens_subtypeVal]
      exact ⟨ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin n)), rfl⟩
  have he := E.connection_mpullback_of_metric_pullback D
    contMDiff_subtype_val.contMDiffAt hi hm hV v
  rw [mfderiv_opens_subtypeVal] at he
  change E.connection (mpullback (𝓡 n) (𝓡 n) (Subtype.val : U → M) V) x v =
    (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))).inverse
      (D.connection V x.val v) at he
  rw [ContinuousLinearMap.inverse_id] at he
  exact he

end PoincareConjecture.M47
