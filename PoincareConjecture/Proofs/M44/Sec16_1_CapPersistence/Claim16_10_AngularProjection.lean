import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_PhysicalAxialPlane
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_CylinderPlaneRank
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_SphereTopology
import PoincareConjecture.Proofs.M44.Mathlib.LocalHomeomorphDerivative

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology ContinuousMap

namespace PoincareConjecture.M44

open M36

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "IC" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)
local notation "e" => EuclideanSpace.basisFun (Fin 3) ℝ

theorem contMDiff_neck_sphere_coordinates
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} (N : EpsilonNeck g)
    {f : UnitTwoSphere → M} (hf : ContMDiff (𝓡 2) (𝓡 3) ∞ f)
    (hmem : ∀ z, f z ∈ N.carrier) :
    ContMDiff (𝓡 2) IC ∞ (N.coordinate_inverse ∘ f) :=
  fun z => (neck_inverse_contMDiffAt N (hmem z)).comp z (hf z)

def neckSphereAngularMap
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} (N : EpsilonNeck g)
    {f : UnitTwoSphere → M} (hf : ContMDiff (𝓡 2) (𝓡 3) ∞ f)
    (hmem : ∀ z, f z ∈ N.carrier) : C(UnitTwoSphere, UnitTwoSphere) :=
  ⟨fun z => (N.coordinate_inverse (f z)).1,
    (contMDiff_neck_sphere_coordinates N hf hmem).fst.continuous⟩

theorem exists_neck_sphere_angular_cutoff {k : ℝ} (hk : 0 < k) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧
      ∀ {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
        [IsManifold (𝓡 3) ∞ M] [T2Space M]
        {g : RiemannianMetric 3 M} (N : EpsilonNeck g), N.epsilon ≤ epsilon0 →
      ∀ (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 3) ∞ f)
        (hmem : ∀ z, f z ∈ N.carrier),
      (∀ z, Function.Injective (mfderiv (𝓡 2) (𝓡 3) f z)) →
      (∀ z, ∀ u v : TangentSpace (𝓡 2) z,
        let Df := mfderiv (𝓡 2) (𝓡 3) f z
        let h := normalizedNeckMetric N
        0 < h.inner (f z) (Df u) (Df u) * h.inner (f z) (Df v) (Df v) -
          (h.inner (f z) (Df u) (Df v)) ^ 2 →
          k < (normalizedNeckConnection N).sectionalCurvature (f z) (Df u) (Df v)) →
      IsLocalHomeomorph (neckSphereAngularMap N hf hmem) := by
  obtain ⟨epsilon0, hepsilon0, hbound⟩ := exists_normalized_neck_axial_cutoff hk
  refine ⟨epsilon0, hepsilon0, ?_⟩
  intro M _ _ _ _ g N hsmall f hf hmem himm hlower
  let H := N.coordinate_inverse ∘ f
  have hH : ContMDiff (𝓡 2) IC ∞ H := contMDiff_neck_sphere_coordinates N hf hmem
  apply Poincare.isLocalHomeomorph_of_mfderiv_bijective hH.fst
  intro z
  let L0 : E2 →L[ℝ] E2 × ℝ := mfderiv (𝓡 2) IC H z
  let L : E2 →L[ℝ] E := cylinderEuclideanEquiv.symm.toContinuousLinearMap.comp L0
  have hz : (H z).2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    (N.coordinate_inverse_mem (f z) (hmem z)).2
  have hzero := zero_mem_centeredNeckDomain N hz
  have hcoord := neck_coordinate_contMDiffAt N (N.coordinate_inverse_mem (f z) (hmem z))
  have hfull : N.coordinate_map ∘ H = f := funext (fun w => neck_coordinate_inverse N (hmem w))
  have hcomp : mfderiv (𝓡 2) (𝓡 3) f z =
      (mfderiv IC (𝓡 3) N.coordinate_map (H z)).comp L0 := by
    have h := mfderiv_comp z (hcoord.mdifferentiableAt (by simp))
      ((hH z).mdifferentiableAt (by simp))
    rw [hfull] at h
    exact h
  have hL0 : Function.Injective L0 := by
    intro a c hac
    apply himm z
    rw [hcomp]
    exact congrArg (mfderiv IC (𝓡 3) N.coordinate_map (H z)) hac
  have hL : Function.Injective L := cylinderEuclideanEquiv.symm.injective.comp hL0
  have hproj : mfderiv (𝓡 2) (𝓡 2) (fun w => (H w).1) z =
      cylinderHorizontalProjection.comp L := by
    change mfderiv (𝓡 2) (𝓡 2) (Prod.fst ∘ H) z = _
    rw [mfderiv_comp z mdifferentiableAt_fst ((hH z).mdifferentiableAt (by simp)), mfderiv_fst]
    ext v
    change (L0 v).1 = (cylinderEuclideanEquiv (cylinderEuclideanEquiv.symm (L0 v))).1
    rw [cylinderEuclideanEquiv.apply_symm_apply]
  have hinj : Function.Injective (cylinderHorizontalProjection.comp L) := by
    by_contra hP
    obtain ⟨⟨a, ha⟩, u, hu, hh, c, hc⟩ := cylinder_axis_and_horizontal_of_rank_drop L hL hP
    let lift := centeredNeckLift N (H z).1 (H z).2
    let A : E →L[ℝ] TangentSpace (𝓡 3) (f z) := mfderiv (𝓡 3) (𝓡 3) lift 0
    have hpoint : lift 0 = f z := by
      change centeredNeckLift N (H z).1 (H z).2 0 = f z
      rw [centeredNeckLift_zero]
      exact neck_coordinate_inverse N (hmem z)
    have hA (v : E) : A v =
        mfderiv IC (𝓡 3) N.coordinate_map (H z) (cylinderEuclideanEquiv v) := by
      change mfderiv (𝓡 3) (𝓡 3) (centeredNeckLift N (H z).1 (H z).2) 0 v = _
      rw [centeredNeckLift_mfderiv N (H z).1 (H z).2 hzero,
        centeredCylinderLift_zero, map_zero,
        ← sphere_chart_center_zero (H z).1, sphere_chart_inverse_mfderiv]
      rfl
    have hAL (v : E2) : A (L v) = mfderiv (𝓡 2) (𝓡 3) f z v := by
      rw [hA, hcomp]
      change mfderiv IC (𝓡 3) N.coordinate_map (H z)
        (cylinderEuclideanEquiv (cylinderEuclideanEquiv.symm (L0 v))) = _
      rw [cylinderEuclideanEquiv.apply_symm_apply]
      rfl
    have ha' : A (e 2) = mfderiv (𝓡 2) (𝓡 3) f z a := by rw [← ha]; exact hAL a
    have hc' : A u = mfderiv (𝓡 2) (𝓡 3) f z c := by rw [← hc]; exact hAL c
    have hax := hbound N hsmall (H z) hz u hu hh
    change 0 < (normalizedNeckMetric N).inner (lift 0) (A (e 2)) (A (e 2)) *
        (normalizedNeckMetric N).inner (lift 0) (A u) (A u) -
          ((normalizedNeckMetric N).inner (lift 0) (A (e 2)) (A u)) ^ 2 ∧
        |(normalizedNeckConnection N).sectionalCurvature (lift 0) (A (e 2)) (A u)| < k at hax
    rw [hpoint, ha', hc'] at hax
    have hlo := hlower z a c hax.1
    exact (not_lt_of_ge hlo.le) ((le_abs_self _).trans_lt hax.2)
  have hangular : Function.Injective (mfderiv (𝓡 2) (𝓡 2) (fun w => (H w).1) z) :=
    hproj ▸ hinj
  let Dangle : E2 →L[ℝ] E2 := mfderiv (𝓡 2) (𝓡 2) (fun w => (H w).1) z
  exact ⟨hangular,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := Dangle.toLinearMap) rfl).mp hangular⟩

end PoincareConjecture.M44
