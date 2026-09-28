import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.LocalIsometry.Transition
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.Quotient.Orientation
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Topology.Covering.Basic









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter PoincareConjecture
open scoped Manifold ContDiff Bundle Topology

namespace Poincare.Geometry.Riemannian.SpaceForm

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

private instance : ConnectedSpace (UnitSphere 3) := by
  apply isConnected_iff_connectedSpace.mp
  apply isConnected_sphere _ _ (by norm_num)
  rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
  norm_num

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]



theorem exists_orthogonal_deck_transformation
    (g : RiemannianMetric 3 M) (q : UnitSphere 3 → M)
    (hq : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ q)
    (hmetric : ∀ x u v, g.inner (q x)
      (mfderiv (𝓡 3) (𝓡 3) q x u) (mfderiv (𝓡 3) (𝓡 3) q x v) =
        (roundSphereMetric 3).inner x u v)
    {x y : UnitSphere 3} (hxy : q x = q y) :
    ∃ L : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4),
      sphereMotion L x = y ∧ ∀ z, q (sphereMotion L z) = q z := by
  let Lx := hq.mfderivToContinuousLinearEquiv (by simp) x
  let Ly := hq.mfderivToContinuousLinearEquiv (by simp) y
  let A : TangentSpace (𝓡 3) x ≃L[ℝ] TangentSpace (𝓡 3) y := Lx.trans Ly.symm
  have hA (u v : TangentSpace (𝓡 3) x) :
      (roundSphereMetric 3).inner y (A u) (A v) =
        (roundSphereMetric 3).inner x u v := by
    rw [← hmetric y (A u) (A v)]
    change g.inner (q y) (Ly (Ly.symm (Lx u))) (Ly (Ly.symm (Lx v))) = _
    rw [Ly.apply_symm_apply, Ly.apply_symm_apply, ← hxy]
    exact hmetric x u v
  obtain ⟨L, hpos, hder⟩ := exists_ambient_sphere_motion_firstOrder x y A hA
  refine ⟨L, hpos, ?_⟩
  have hcomp : ContMDiff (𝓡 3) (𝓡 3) ∞ (q ∘ sphereMotion L) :=
    hq.contMDiff.comp (sphereMotion L).contMDiff
  have hcompmetric (z : UnitSphere 3) (u v : TangentSpace (𝓡 3) z) :
      (roundSphereMetric 3).inner z u v = g.inner ((q ∘ sphereMotion L) z)
        (mfderiv (𝓡 3) (𝓡 3) (q ∘ sphereMotion L) z u)
        (mfderiv (𝓡 3) (𝓡 3) (q ∘ sphereMotion L) z v) := by
    rw [mfderiv_comp z (hq.mdifferentiable (by simp) _)
      ((sphereMotion L).contMDiffAt.mdifferentiableAt (by simp))]
    exact (sphereMotion_inner L z u v).symm.trans (hmetric _ _ _).symm
  have hcompder : mfderiv (𝓡 3) (𝓡 3) (q ∘ sphereMotion L) x =
      mfderiv (𝓡 3) (𝓡 3) q x := by
    rw [mfderiv_comp x (hq.mdifferentiable (by simp) _)
      ((sphereMotion L).contMDiffAt.mdifferentiableAt (by simp))]
    ext v
    change mfderiv (𝓡 3) (𝓡 3) q (sphereMotion L x)
      (mfderiv (𝓡 3) (𝓡 3) (sphereMotion L) x v) = _
    rw [hder]
    erw [hpos]
    change Ly (Ly.symm (Lx v)) = Lx v
    exact Ly.apply_symm_apply (Lx v)
  have heq := PoincareConjecture.SpaceForm.local_isometry_eqOn_of_firstOrder
    (roundSphereMetric 3) g isOpen_univ isPreconnected_univ
    hcomp.contMDiffOn hq.contMDiff.contMDiffOn
    (fun z _ u v => hcompmetric z u v)
    (fun z _ u v => (hmetric z u v).symm) (mem_univ x)
    (by simpa only [Function.comp_apply, hpos] using hxy.symm) hcompder
  exact fun z => heq (mem_univ z)

private theorem sphereMotion_one (x : UnitSphere 3) :
    sphereMotion (1 : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4)) x = x :=
  Subtype.ext rfl

private theorem sphereMotion_mul
    (L K : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4))
    (x : UnitSphere 3) :
    sphereMotion (L * K) x = sphereMotion L (sphereMotion K x) := Subtype.ext rfl

private theorem sphereMotion_inv
    (L : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4))
    (x : UnitSphere 3) : sphereMotion L (sphereMotion L⁻¹ x) = x :=
  Subtype.ext (L.apply_symm_apply x)

private theorem sphereMotion_injective :
    Function.Injective (fun L : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin 4) => (sphereMotion L : UnitSphere 3 → UnitSphere 3)) := by
  intro L K h
  apply LinearIsometryEquiv.ext
  intro v
  by_cases hv : v = 0
  · simp [hv]
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  let x : UnitSphere 3 := ⟨‖v‖⁻¹ • v, by
    rw [Metric.mem_sphere, dist_zero_right, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg v)), inv_mul_cancel₀ hn]⟩
  have hx : L (x : EuclideanSpace ℝ (Fin 4)) = K x :=
    congrArg Subtype.val (congrFun h x)
  have hscale : ‖v‖ • (x : EuclideanSpace ℝ (Fin 4)) = v := by
    change ‖v‖ • (‖v‖⁻¹ • v) = v
    rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
  calc
    L v = L (‖v‖ • (x : EuclideanSpace ℝ (Fin 4))) := congrArg L hscale.symm
    _ = ‖v‖ • L (x : EuclideanSpace ℝ (Fin 4)) := L.map_smul _ _
    _ = ‖v‖ • K (x : EuclideanSpace ℝ (Fin 4)) := congrArg (‖v‖ • ·) hx
    _ = K (‖v‖ • (x : EuclideanSpace ℝ (Fin 4))) := (K.map_smul _ _).symm
    _ = K v := congrArg K hscale


def orthogonalDeckGroup (q : UnitSphere 3 → M) :
    Subgroup (EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4)) where
  carrier := {L | ∀ x, q (sphereMotion L x) = q x}
  one_mem' := fun x => congrArg q (sphereMotion_one x)
  mul_mem' := by
    intro L K hL hK x
    rw [sphereMotion_mul, hL, hK]
  inv_mem' := by
    intro L hL x
    have h := hL (sphereMotion L⁻¹ x)
    rw [sphereMotion_inv] at h
    exact h.symm


instance orthogonalDeckGroup_mulAction (q : UnitSphere 3 → M) :
    MulAction (orthogonalDeckGroup q) (UnitSphere 3) where
  smul L x := sphereMotion L.val x
  one_smul := sphereMotion_one
  mul_smul L K x := sphereMotion_mul L.val K.val x

omit [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M] in
@[simp] theorem orthogonalDeckGroup_smul (q : UnitSphere 3 → M)
    (L : orthogonalDeckGroup q) (x : UnitSphere 3) :
    L • x = sphereMotion L.val x := rfl

omit [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M] in
theorem orthogonalDeckGroup_map_smul (q : UnitSphere 3 → M)
    (L : orthogonalDeckGroup q) (x : UnitSphere 3) : q (L • x) = q x :=
  L.property x

omit [IsManifold (𝓡 3) ∞ M] in

theorem orthogonalDeckGroup_eval_injective (q : UnitSphere 3 → M)
    (hq : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ q) (x : UnitSphere 3) :
    Function.Injective (fun L : orthogonalDeckGroup q => L • x) := by
  intro L K hLK
  apply Subtype.ext
  apply sphereMotion_injective
  have hcov : IsCoveringMap q := isLocalHomeomorph_iff_isCoveringMap.mp hq.isLocalHomeomorph
  exact hcov.eq_of_comp_eq (sphereMotion L.val).continuous (sphereMotion K.val).continuous
    (funext fun z => (L.property z).trans (K.property z).symm) x hLK

omit [IsManifold (𝓡 3) ∞ M] in

theorem orthogonalDeckGroup_free (q : UnitSphere 3 → M)
    (hq : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ q)
    (L : orthogonalDeckGroup q) (x : UnitSphere 3) (hL : L • x = x) : L = 1 :=
  orthogonalDeckGroup_eval_injective q hq x (hL.trans (one_smul _ x).symm)

omit [IsManifold (𝓡 3) ∞ M] in

theorem orthogonalDeckGroup_finite (q : UnitSphere 3 → M)
    (hq : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ q) : Finite (orthogonalDeckGroup q) := by
  let x : UnitSphere 3 := ⟨EuclideanSpace.single 0 1, by simp [UnitSphere]⟩
  have hcov : IsCoveringMap q := isLocalHomeomorph_iff_isCoveringMap.mp hq.isLocalHomeomorph
  let : DiscreteTopology (q ⁻¹' {q x}) := (hcov (q x)).discreteTopology_fiber
  have hcompact : IsCompact (q ⁻¹' {q x}) :=
    (isClosed_singleton.preimage hq.contMDiff.continuous).isCompact
  let : CompactSpace (q ⁻¹' {q x}) := isCompact_iff_compactSpace.mp hcompact
  let : Finite (q ⁻¹' {q x}) := finite_of_compact_of_discrete
  let ev : orthogonalDeckGroup q → q ⁻¹' {q x} :=
    fun L => ⟨L • x, orthogonalDeckGroup_map_smul q L x⟩
  apply Finite.of_injective ev
  intro L K h
  exact orthogonalDeckGroup_eval_injective q hq x (congrArg Subtype.val h)


theorem orthogonalDeckGroup_orbit_iff
    (g : RiemannianMetric 3 M) (q : UnitSphere 3 → M)
    (hq : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ q)
    (hmetric : ∀ x u v, g.inner (q x)
      (mfderiv (𝓡 3) (𝓡 3) q x u) (mfderiv (𝓡 3) (𝓡 3) q x v) =
        (roundSphereMetric 3).inner x u v)
    (x y : UnitSphere 3) : q x = q y ↔ ∃ L : orthogonalDeckGroup q, L • x = y := by
  constructor
  · intro hxy
    obtain ⟨L, hLxy, hL⟩ := exists_orthogonal_deck_transformation g q hq hmetric hxy
    exact ⟨⟨L, hL⟩, hLxy⟩
  · rintro ⟨L, rfl⟩
    exact (orthogonalDeckGroup_map_smul q L x).symm


def sphereMotionMatrix
    (L : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4)) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  LinearMap.toMatrix (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis L.toLinearEquiv.toLinearMap

@[simp] theorem sphereMotionMatrix_one :
    sphereMotionMatrix (1 : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin 4)) = 1 :=
  LinearMap.toMatrix_id _

@[simp] theorem sphereMotionMatrix_mul
    (L K : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4)) :
    sphereMotionMatrix (L * K) = sphereMotionMatrix L * sphereMotionMatrix K :=
  LinearMap.toMatrix_comp _ _ _ _ _

theorem sphereMotionMatrix_orthogonal
    (L : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4)) :
    (sphereMotionMatrix L).transpose * sphereMotionMatrix L = 1 :=
  (Matrix.mem_orthogonalGroup_iff' _ _).mp
    (L.toMatrix_mem_unitaryGroup (EuclideanSpace.basisFun (Fin 4) ℝ)
      (EuclideanSpace.basisFun (Fin 4) ℝ))

theorem sphereMotionMatrix_mulVec
    (L : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4))
    (v : EuclideanSpace ℝ (Fin 4)) :
    (sphereMotionMatrix L).mulVec (WithLp.ofLp v) = WithLp.ofLp (L v) := by
  have h := LinearMap.toMatrix_mulVec_repr (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis L.toLinearEquiv.toLinearMap v
  have hrepr (w : EuclideanSpace ℝ (Fin 4)) :
      ⇑((EuclideanSpace.basisFun (Fin 4) ℝ).toBasis.repr w) = WithLp.ofLp w := by
    funext i
    rw [OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr]
  rw [hrepr v, hrepr (L.toLinearEquiv.toLinearMap v)] at h
  exact h

omit [IsManifold (𝓡 3) ∞ M] in

theorem orthogonalDeckGroup_det_one (q : UnitSphere 3 → M)
    (hq : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ q) (L : orthogonalDeckGroup q) :
    (sphereMotionMatrix L.val).det = 1 := by
  by_cases hL : L = 1
  · subst L
    change (sphereMotionMatrix (1 : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin 4))).det = 1
    rw [sphereMotionMatrix_one, Matrix.det_one]
  apply det_eq_one_of_no_unit_fixed_vector
  · exact mul_eq_one_comm.mp (sphereMotionMatrix_orthogonal L.val)
  · change Even 4
    exact ⟨2, rfl⟩
  · intro v hv hfixed
    let x : UnitSphere 3 := ⟨v, by simpa only [Metric.mem_sphere, dist_zero_right] using hv⟩
    apply hL
    apply orthogonalDeckGroup_free q hq L x
    apply Subtype.ext
    apply WithLp.ofLp_injective 2
    exact (sphereMotionMatrix_mulVec L.val v).symm.trans hfixed

omit [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M] in

theorem orthogonalDeckGroup_action_representation (q : UnitSphere 3 → M)
    (L : orthogonalDeckGroup q) (x : UnitSphere 3) :
    WithLp.ofLp ((L • x : UnitSphere 3) : EuclideanSpace ℝ (Fin 4)) =
      (sphereMotionMatrix L.val).mulVec (WithLp.ofLp (x : EuclideanSpace ℝ (Fin 4))) :=
  (sphereMotionMatrix_mulVec L.val x).symm

omit [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M] in

theorem orthogonalDeckGroup_dist_smul (q : UnitSphere 3 → M)
    (L : orthogonalDeckGroup q) (x y : UnitSphere 3) :
    dist (L • x) (L • y) = dist x y :=
  L.val.isometry.dist_eq x y

omit [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M] in

theorem orthogonalDeckGroup_contMDiff (q : UnitSphere 3 → M)
    (L : orthogonalDeckGroup q) :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (fun x : UnitSphere 3 => L • x) :=
  (sphereMotion L.val).contMDiff

end Poincare.Geometry.Riemannian.SpaceForm
