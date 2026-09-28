import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Geometry.NeckLevels.Differential
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Overlap.ProjectionDerivative
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.RegularLevelMap
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.InverseFunction.SmoothInverse

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function TopologicalSpace
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

theorem hasDerivAt_comp_axis (N : EpsilonNeck g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ f) (q : UnitTwoSphere)
    {t : ℝ} (ht : t ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    HasDerivAt (fun s : ℝ => f (N.coordinate_map (q, s)))
      (mvfderiv (𝓡 3) f (N.coordinate_map (q, t))
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map (q, t) (0, 1))) t := by
  have hmap := (N.coordinate_map_smooth.contMDiffAt
    (N.cylinderDomain_open.mem_nhds
      (show (q, t) ∈ N.cylinderDomain from ⟨mem_univ q, ht⟩))).mdifferentiableAt (by simp)
  have hpair := (hasMFDerivAt_const (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 2) q t).prodMk
    (hasMFDerivAt_id (I := 𝓘(ℝ, ℝ)) t)
  have hcomp := ((hf _).mdifferentiableAt (by simp)).hasMFDerivAt.comp t
    (hmap.hasMFDerivAt.comp t hpair)
  exact hcomp.hasFDerivAt.hasDerivAt

theorem regularLevel_sphereProjection_contMDiff
    (N : EpsilonNeck g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ f) (U : Opens M)
    (hU : (U : Set M) ⊆ N.carrier)
    (hreg : ∀ x ∈ U, mfderiv (𝓡 3) 𝓘(ℝ, ℝ) f x ≠ 0) (c : ℝ) :
    letI := openLevelSetChartedSpace hf U hreg 2 c
    ContMDiff (𝓡 2) (𝓡 2) ∞
      (fun z : openLevelSet f U c => (N.coordinate_inverse (openLevelIncl f U c z)).1) := by
  letI := openLevelSetChartedSpace hf U hreg 2 c
  intro z
  exact contMDiffAt_fst.comp z
    ((N.coordinate_inverse_smooth.contMDiffAt
      (N.carrier_open.mem_nhds (hU z.1.2))).comp z
        (contMDiff_openLevelIncl hf U hreg 2 c z))

theorem regularLevel_sphereProjection_bijective_mfderiv
    (N : EpsilonNeck g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ f) (U : Opens M)
    (hU : (U : Set M) ⊆ N.carrier)
    (hreg : ∀ x ∈ U, mfderiv (𝓡 3) 𝓘(ℝ, ℝ) f x ≠ 0) (c : ℝ)
    (haxial : ∀ x ∈ U,
      mvfderiv (𝓡 3) f x
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
          N.coordinate_map (N.coordinate_inverse x) (0, 1)) ≠ 0) :
    letI := openLevelSetChartedSpace hf U hreg 2 c
    ∀ z : openLevelSet f U c, Bijective
      (mfderiv (𝓡 2) (𝓡 2)
        (fun y : openLevelSet f U c => (N.coordinate_inverse (openLevelIncl f U c y)).1) z) := by
  letI := openLevelSetChartedSpace hf U hreg 2 c
  intro z
  let P : openLevelSet f U c → UnitTwoSphere :=
    fun y => (N.coordinate_inverse (openLevelIncl f U c y)).1
  let A := mfderiv (𝓡 2) (𝓡 2) P z
  have hinj : Injective A := by
    apply (injective_iff_map_eq_zero A).mpr
    intro v hv
    let x := openLevelIncl f U c z
    let w := mfderiv (𝓡 2) (𝓡 3) (openLevelIncl f U c) z v
    let a := mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) N.coordinate_inverse x w
    have hx : x ∈ N.carrier := hU z.1.2
    have hinc := (contMDiff_openLevelIncl hf U hreg 2 c z).mdifferentiableAt (by simp)
    have hinv := (N.coordinate_inverse_smooth.contMDiffAt
      (N.carrier_open.mem_nhds hx)).mdifferentiableAt (by simp)
    have hcomp := hinv.hasMFDerivAt.comp z hinc.hasMFDerivAt
    have hfst := (hasMFDerivAt_fst (I := 𝓡 2) (I' := 𝓘(ℝ, ℝ))
      (N.coordinate_inverse x)).comp z hcomp
    have ha1 : a.1 = 0 := by
      have hd := congrArg (fun L => L v) hfst.mfderiv
      exact hd.symm.trans hv
    have hker : mvfderiv (𝓡 3) f x w = 0 := by
      have hr := range_mfderiv_openLevelIncl hf U hreg 2 c z
      have hw : w ∈ (mfderiv (𝓡 2) (𝓡 3) (openLevelIncl f U c) z).range := ⟨v, rfl⟩
      rw [hr] at hw
      change (NormedSpace.fromTangentSpace (f x))
        (mfderiv (𝓡 3) 𝓘(ℝ, ℝ) f x w) = 0
      rw [show mfderiv (𝓡 3) 𝓘(ℝ, ℝ) f x w = 0 from hw, map_zero]
    have haeq : a = a.2 • (0, 1) := by
      change a = (a.2 • (0 : EuclideanSpace ℝ (Fin 2)), a.2 * (1 : ℝ))
      simp only [smul_zero, mul_one]
      apply Prod.ext
      · exact ha1
      · rfl
    have hwback :
        mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
          N.coordinate_map (N.coordinate_inverse x) a = w :=
      N.coordinate_map_mfderiv_inverse_prod hx w
    have hprod : a.2 * mvfderiv (𝓡 3) f x
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
          N.coordinate_map (N.coordinate_inverse x) (0, 1)) = 0 := by
      rw [← hwback, haeq, map_smul, map_smul, smul_eq_mul] at hker
      exact hker
    have ha2 : a.2 = 0 := (mul_eq_zero.mp hprod).resolve_right (haxial x z.1.2)
    have hazero : a = 0 := Prod.ext ha1 ha2
    rw [hazero, map_zero] at hwback
    exact (injective_mfderiv_openLevelIncl hf U hreg 2 c z)
      (show mfderiv (𝓡 2) (𝓡 3) (openLevelIncl f U c) z v =
          mfderiv (𝓡 2) (𝓡 3) (openLevelIncl f U c) z 0 by
        rw [map_zero]
        exact hwback.symm)
  let : FiniteDimensional ℝ (TangentSpace (𝓡 2) z) := by
    unfold TangentSpace
    infer_instance
  exact ⟨hinj, (LinearMap.injective_iff_surjective (f := A.toLinearMap)).mp hinj⟩

end PoincareConjecture.EpsilonNeck
