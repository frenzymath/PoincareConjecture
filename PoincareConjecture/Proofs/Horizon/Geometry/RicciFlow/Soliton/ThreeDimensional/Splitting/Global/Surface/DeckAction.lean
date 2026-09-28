import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Surface.Cover
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Surface.DeckCardinality
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.LocalIsometry.Transition
import Mathlib.Topology.Covering.Basic

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter PoincareConjecture Poincare.Geometry.Riemannian.SpaceForm
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RicciFlow.Splitting

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

private instance : ConnectedSpace (UnitSphere 2) := by
  apply isConnected_iff_connectedSpace.mp
  apply isConnected_sphere _ _ (by norm_num)
  rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
  norm_num

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

theorem exists_orthogonal_surface_deck_transformation
    (g : RiemannianMetric 2 M) (q : UnitSphere 2 → M)
    (hq : IsLocalDiffeomorph (𝓡 2) (𝓡 2) ∞ q)
    (hmetric : ∀ x u v, g.inner (q x)
      (mfderiv (𝓡 2) (𝓡 2) q x u) (mfderiv (𝓡 2) (𝓡 2) q x v) =
        (roundSphereMetric 2).inner x u v)
    {x y : UnitSphere 2} (hxy : q x = q y) :
    ∃ L : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3),
      sphereMotion L x = y ∧ ∀ z, q (sphereMotion L z) = q z := by
  let Lx := hq.mfderivToContinuousLinearEquiv (by simp) x
  let Ly := hq.mfderivToContinuousLinearEquiv (by simp) y
  let A : TangentSpace (𝓡 2) x ≃L[ℝ] TangentSpace (𝓡 2) y := Lx.trans Ly.symm
  have hA (u v : TangentSpace (𝓡 2) x) :
      (roundSphereMetric 2).inner y (A u) (A v) =
        (roundSphereMetric 2).inner x u v := by
    rw [← hmetric y (A u) (A v)]
    change g.inner (q y) (Ly (Ly.symm (Lx u))) (Ly (Ly.symm (Lx v))) = _
    rw [Ly.apply_symm_apply, Ly.apply_symm_apply, ← hxy]
    exact hmetric x u v
  obtain ⟨L, hpos, hder⟩ := exists_ambient_sphere_motion_firstOrder x y A hA
  refine ⟨L, hpos, ?_⟩
  have hcomp : ContMDiff (𝓡 2) (𝓡 2) ∞ (q ∘ sphereMotion L) :=
    hq.contMDiff.comp (sphereMotion L).contMDiff
  have hcompmetric (z : UnitSphere 2) (u v : TangentSpace (𝓡 2) z) :
      (roundSphereMetric 2).inner z u v = g.inner ((q ∘ sphereMotion L) z)
        (mfderiv (𝓡 2) (𝓡 2) (q ∘ sphereMotion L) z u)
        (mfderiv (𝓡 2) (𝓡 2) (q ∘ sphereMotion L) z v) := by
    rw [mfderiv_comp z (hq.mdifferentiable (by simp) _)
      ((sphereMotion L).contMDiffAt.mdifferentiableAt (by simp))]
    exact (sphereMotion_inner L z u v).symm.trans (hmetric _ _ _).symm
  have hcompder : mfderiv (𝓡 2) (𝓡 2) (q ∘ sphereMotion L) x =
      mfderiv (𝓡 2) (𝓡 2) q x := by
    rw [mfderiv_comp x (hq.mdifferentiable (by simp) _)
      ((sphereMotion L).contMDiffAt.mdifferentiableAt (by simp))]
    ext v
    change mfderiv (𝓡 2) (𝓡 2) q (sphereMotion L x)
      (mfderiv (𝓡 2) (𝓡 2) (sphereMotion L) x v) = _
    rw [hder]
    erw [hpos]
    change Ly (Ly.symm (Lx v)) = Lx v
    exact Ly.apply_symm_apply (Lx v)
  have heq := PoincareConjecture.SpaceForm.local_isometry_eqOn_of_firstOrder
    (roundSphereMetric 2) g isOpen_univ isPreconnected_univ
    hcomp.contMDiffOn hq.contMDiff.contMDiffOn
    (fun z _ u v => hcompmetric z u v)
    (fun z _ u v => (hmetric z u v).symm) (mem_univ x)
    (by simpa only [Function.comp_apply, hpos] using hxy.symm) hcompder
  exact fun z => heq (mem_univ z)

private theorem surfaceMotion_one (x : UnitSphere 2) :
    sphereMotion (1 : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) x = x :=
  Subtype.ext rfl

private theorem surfaceMotion_mul
    (L K : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (x : UnitSphere 2) :
    sphereMotion (L * K) x = sphereMotion L (sphereMotion K x) := Subtype.ext rfl

private theorem surfaceMotion_inv
    (L : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (x : UnitSphere 2) : sphereMotion L (sphereMotion L⁻¹ x) = x :=
  Subtype.ext (L.apply_symm_apply x)

theorem surfaceMotion_injective :
    Function.Injective (fun L : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin 3) => (sphereMotion L : UnitSphere 2 → UnitSphere 2)) := by
  intro L K h
  apply LinearIsometryEquiv.ext
  intro v
  by_cases hv : v = 0
  · simp [hv]
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  let x : UnitSphere 2 := ⟨‖v‖⁻¹ • v, by
    rw [Metric.mem_sphere, dist_zero_right, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg v)), inv_mul_cancel₀ hn]⟩
  have hx : L (x : EuclideanSpace ℝ (Fin 3)) = K x :=
    congrArg Subtype.val (congrFun h x)
  have hscale : ‖v‖ • (x : EuclideanSpace ℝ (Fin 3)) = v := by
    change ‖v‖ • (‖v‖⁻¹ • v) = v
    rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
  calc
    L v = L (‖v‖ • (x : EuclideanSpace ℝ (Fin 3))) := congrArg L hscale.symm
    _ = ‖v‖ • L (x : EuclideanSpace ℝ (Fin 3)) := L.map_smul _ _
    _ = ‖v‖ • K (x : EuclideanSpace ℝ (Fin 3)) := congrArg (‖v‖ • ·) hx
    _ = K (‖v‖ • (x : EuclideanSpace ℝ (Fin 3))) := (K.map_smul _ _).symm
    _ = K v := congrArg K hscale

def orthogonalSurfaceDeckGroup (q : UnitSphere 2 → M) :
    Subgroup (EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) where
  carrier := {L | ∀ x, q (sphereMotion L x) = q x}
  one_mem' := fun x => congrArg q (surfaceMotion_one x)
  mul_mem' := by
    intro L K hL hK x
    rw [surfaceMotion_mul, hL, hK]
  inv_mem' := by
    intro L hL x
    have h := hL (sphereMotion L⁻¹ x)
    rw [surfaceMotion_inv] at h
    exact h.symm

instance orthogonalSurfaceDeckGroup_mulAction (q : UnitSphere 2 → M) :
    MulAction (orthogonalSurfaceDeckGroup q) (UnitSphere 2) where
  smul L x := sphereMotion L.val x
  one_smul := surfaceMotion_one
  mul_smul L K x := surfaceMotion_mul L.val K.val x

omit [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M] in
@[simp] theorem orthogonalSurfaceDeckGroup_smul (q : UnitSphere 2 → M)
    (L : orthogonalSurfaceDeckGroup q) (x : UnitSphere 2) :
    L • x = sphereMotion L.val x := rfl

omit [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M] in
theorem orthogonalSurfaceDeckGroup_map_smul (q : UnitSphere 2 → M)
    (L : orthogonalSurfaceDeckGroup q) (x : UnitSphere 2) : q (L • x) = q x :=
  L.property x

omit [IsManifold (𝓡 2) ∞ M] in

theorem orthogonalSurfaceDeckGroup_eval_injective (q : UnitSphere 2 → M)
    (hq : IsLocalDiffeomorph (𝓡 2) (𝓡 2) ∞ q) (x : UnitSphere 2) :
    Function.Injective (fun L : orthogonalSurfaceDeckGroup q => L • x) := by
  intro L K hLK
  apply Subtype.ext
  apply surfaceMotion_injective
  have hcov : IsCoveringMap q := isLocalHomeomorph_iff_isCoveringMap.mp hq.isLocalHomeomorph
  exact hcov.eq_of_comp_eq (sphereMotion L.val).continuous (sphereMotion K.val).continuous
    (funext fun z => (L.property z).trans (K.property z).symm) x hLK

omit [IsManifold (𝓡 2) ∞ M] in

theorem orthogonalSurfaceDeckGroup_free (q : UnitSphere 2 → M)
    (hq : IsLocalDiffeomorph (𝓡 2) (𝓡 2) ∞ q)
    (L : orthogonalSurfaceDeckGroup q) (x : UnitSphere 2) (hL : L • x = x) : L = 1 :=
  orthogonalSurfaceDeckGroup_eval_injective q hq x (hL.trans (one_smul _ x).symm)

omit [IsManifold (𝓡 2) ∞ M] in

theorem orthogonalSurfaceDeckGroup_finite (q : UnitSphere 2 → M)
    (hq : IsLocalDiffeomorph (𝓡 2) (𝓡 2) ∞ q) :
    Finite (orthogonalSurfaceDeckGroup q) := by
  let x : UnitSphere 2 := ⟨EuclideanSpace.single 0 1, by simp [UnitSphere]⟩
  have hcov : IsCoveringMap q := isLocalHomeomorph_iff_isCoveringMap.mp hq.isLocalHomeomorph
  let : DiscreteTopology (q ⁻¹' {q x}) := (hcov (q x)).discreteTopology_fiber
  have hcompact : IsCompact (q ⁻¹' {q x}) :=
    (isClosed_singleton.preimage hq.contMDiff.continuous).isCompact
  let : CompactSpace (q ⁻¹' {q x}) := isCompact_iff_compactSpace.mp hcompact
  let : Finite (q ⁻¹' {q x}) := finite_of_compact_of_discrete
  let ev : orthogonalSurfaceDeckGroup q → q ⁻¹' {q x} :=
    fun L => ⟨L • x, orthogonalSurfaceDeckGroup_map_smul q L x⟩
  apply Finite.of_injective ev
  intro L K h
  exact orthogonalSurfaceDeckGroup_eval_injective q hq x (congrArg Subtype.val h)

theorem orthogonalSurfaceDeckGroup_orbit_iff
    (g : RiemannianMetric 2 M) (q : UnitSphere 2 → M)
    (hq : IsLocalDiffeomorph (𝓡 2) (𝓡 2) ∞ q)
    (hmetric : ∀ x u v, g.inner (q x)
      (mfderiv (𝓡 2) (𝓡 2) q x u) (mfderiv (𝓡 2) (𝓡 2) q x v) =
        (roundSphereMetric 2).inner x u v)
    (x y : UnitSphere 2) :
    q x = q y ↔ ∃ L : orthogonalSurfaceDeckGroup q, L • x = y := by
  constructor
  · intro hxy
    obtain ⟨L, hLxy, hL⟩ := exists_orthogonal_surface_deck_transformation g q hq hmetric hxy
    exact ⟨⟨L, hL⟩, hLxy⟩
  · rintro ⟨L, rfl⟩
    exact (orthogonalSurfaceDeckGroup_map_smul q L x).symm

omit [IsManifold (𝓡 2) ∞ M] in
theorem orthogonalSurfaceDeckGroup_no_unit_fixed_vector (q : UnitSphere 2 → M)
    (hq : IsLocalDiffeomorph (𝓡 2) (𝓡 2) ∞ q)
    (L : orthogonalSurfaceDeckGroup q) (hL : L ≠ 1)
    (x : EuclideanSpace ℝ (Fin 3)) (hx : ‖x‖ = 1) : L.val x ≠ x := by
  intro hfix
  let y : UnitSphere 2 := ⟨x, by simpa only [Metric.mem_sphere, dist_zero_right] using hx⟩
  exact hL (orthogonalSurfaceDeckGroup_free q hq L y (Subtype.ext hfix))

omit [IsManifold (𝓡 2) ∞ M] in

theorem orthogonalSurfaceDeckGroup_card_le_two (q : UnitSphere 2 → M)
    (hq : IsLocalDiffeomorph (𝓡 2) (𝓡 2) ∞ q) :
    Nat.card (orthogonalSurfaceDeckGroup q) ≤ 2 :=
  free_orthogonalThree_subgroup_card_le_two (orthogonalSurfaceDeckGroup q)
    (orthogonalSurfaceDeckGroup_no_unit_fixed_vector q hq)

omit [IsManifold (𝓡 2) ∞ M] in

theorem orthogonalSurfaceDeckGroup_eq_antipodal (q : UnitSphere 2 → M)
    (hq : IsLocalDiffeomorph (𝓡 2) (𝓡 2) ∞ q)
    (L : orthogonalSurfaceDeckGroup q) (hL : L ≠ 1) :
    L.val = LinearIsometryEquiv.neg ℝ :=
  free_orthogonalThree_subgroup_eq_antipodal (orthogonalSurfaceDeckGroup q)
    (orthogonalSurfaceDeckGroup_no_unit_fixed_vector q hq) L hL

omit [IsManifold (𝓡 2) ∞ M] in
theorem orthogonalSurfaceDeckGroup_smul_eq_neg (q : UnitSphere 2 → M)
    (hq : IsLocalDiffeomorph (𝓡 2) (𝓡 2) ∞ q)
    (L : orthogonalSurfaceDeckGroup q) (hL : L ≠ 1) (x : UnitSphere 2) : L • x = -x := by
  apply Subtype.ext
  change L.val (x : EuclideanSpace ℝ (Fin 3)) = -x.val
  rw [orthogonalSurfaceDeckGroup_eq_antipodal q hq L hL]
  rfl

theorem orthogonalSurfaceDeckGroup_fiber_dichotomy
    (g : RiemannianMetric 2 M) (q : UnitSphere 2 → M)
    (hq : IsLocalDiffeomorph (𝓡 2) (𝓡 2) ∞ q)
    (hmetric : ∀ x u v, g.inner (q x)
      (mfderiv (𝓡 2) (𝓡 2) q x u) (mfderiv (𝓡 2) (𝓡 2) q x v) =
        (roundSphereMetric 2).inner x u v) :
    Function.Injective q ∨ ∀ x y, q x = q y ↔ y = x ∨ y = -x := by
  classical
  by_cases htrivial : ∀ L : orthogonalSurfaceDeckGroup q, L = 1
  · left
    intro x y hxy
    obtain ⟨L, hL⟩ := (orthogonalSurfaceDeckGroup_orbit_iff g q hq hmetric x y).mp hxy
    simpa only [htrivial L, one_smul] using hL
  · push Not at htrivial
    obtain ⟨L, hL⟩ := htrivial
    right
    intro x y
    constructor
    · intro hxy
      obtain ⟨K, hK⟩ := (orthogonalSurfaceDeckGroup_orbit_iff g q hq hmetric x y).mp hxy
      by_cases hKone : K = 1
      · left
        simpa only [hKone, one_smul] using hK.symm
      · exact Or.inr (hK.symm.trans (orthogonalSurfaceDeckGroup_smul_eq_neg q hq K hKone x))
    · rintro (rfl | rfl)
      · rfl
      · exact (orthogonalSurfaceDeckGroup_orbit_iff g q hq hmetric x (-x)).mpr
          ⟨L, orthogonalSurfaceDeckGroup_smul_eq_neg q hq L hL x⟩

omit [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M] in

theorem orthogonalSurfaceDeckGroup_dist_smul (q : UnitSphere 2 → M)
    (L : orthogonalSurfaceDeckGroup q) (x y : UnitSphere 2) :
    dist (L • x) (L • y) = dist x y :=
  L.val.isometry.dist_eq x y

omit [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M] in

theorem orthogonalSurfaceDeckGroup_contMDiff (q : UnitSphere 2 → M)
    (L : orthogonalSurfaceDeckGroup q) :
    ContMDiff (𝓡 2) (𝓡 2) ∞ (fun x : UnitSphere 2 => L • x) :=
  (sphereMotion L.val).contMDiff

end PoincareConjecture.RicciFlow.Splitting
