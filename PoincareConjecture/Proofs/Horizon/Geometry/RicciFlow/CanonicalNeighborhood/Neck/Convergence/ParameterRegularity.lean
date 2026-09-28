import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Convergence.CylinderCoefficients
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Convergence.Embedding

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem cylinderChart_symm_isInvertible_mfderiv
    (q : UnitTwoSphere) (p : RoundCylinderCoordinates) :
    (mfderiv 𝓘(ℝ, RoundCylinderCoordinates) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      (fun y : RoundCylinderCoordinates =>
        ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm y.1, y.2)) p).IsInvertible := by
  have hp : p ∈ (extChartAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (q, (0 : ℝ))).target := by
    simp [roundCylinder_sphereChart_target]
  have h := isInvertible_mfderivWithin_extChartAt_symm hp
  have hrange : range ((𝓡 2).prod 𝓘(ℝ, ℝ)) = univ := by
    change range (id : RoundCylinderCoordinates → RoundCylinderCoordinates) = univ
    exact range_id
  rw [hrange, mfderivWithin_univ] at h
  convert! h using 1

namespace PointedGeometricConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space

theorem eventually_cylinder_parametrizations_regular
    {a b : ℝ} {S : PointedFlowSequence 3 a b}
    (G : PointedGeometricConvergence S) (hzero : a < 0 ∧ 0 < b)
    (Φ : RoundCylinderSpace ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ G.limitCarrier.carrier)
    {K : Set RoundCylinderCoordinates} (hK : IsCompact K) :
    ∀ᶠ i in atTop, ∀ q : UnitTwoSphere,
      ∃ U : Set RoundCylinderCoordinates, IsOpen U ∧ K ⊆ U ∧
        ContMDiffOn 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) ∞
          (fun y => ((G.embedding i).toFun
            (0, Φ ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm y.1, y.2))).2) U ∧
        ∀ y ∈ U, (mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3)
          (fun z => ((G.embedding i).toFun
            (0, Φ ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm z.1, z.2))).2) y).IsInvertible := by
  have hcompact : IsCompact (univ ×ˢ (Prod.snd '' K) : Set RoundCylinderSpace) :=
    isCompact_univ.prod (hK.image continuous_snd)
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset (hcompact.image Φ.continuous)
  filter_upwards [eventually_ge_atTop j] with i hji q
  let c : RoundCylinderCoordinates → RoundCylinderSpace :=
    fun y => ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm y.1, y.2)
  let f : RoundCylinderCoordinates → G.limitCarrier.carrier := Φ ∘ c
  let e : G.limitCarrier.carrier → (S.carrier (G.subsequence i)).carrier :=
    fun x => ((G.embedding i).toFun (0, x)).2
  let U := f ⁻¹' G.exhaustion j
  have hf : ContMDiff 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) ∞ f :=
    Φ.contMDiff.comp (cylinderChart_symm_smooth q)
  have hU : IsOpen U := (G.exhaustion_open j).preimage hf.continuous
  have hKU : K ⊆ U := by
    intro y hy
    exact hj (mem_image_of_mem Φ ⟨mem_univ _, mem_image_of_mem Prod.snd hy⟩)
  have hmem (y : RoundCylinderCoordinates) (hy : y ∈ U) : f y ∈ G.exhaustion i :=
    G.exhaustion_monotone hji hy
  have he (y : RoundCylinderCoordinates) (hy : y ∈ U) :
      ContMDiffAt (𝓡 3) (𝓡 3) ∞ e (f y) :=
    (G.embedding i).spatialMap_contMDiffAt (G.exhaustion_open i) hzero (hmem y hy)
  refine ⟨U, hU, hKU, ?_, ?_⟩
  · intro y hy
    exact ((he y hy).comp y (hf y)).contMDiffWithinAt
  · intro y hy
    have hi : (mfderiv (𝓡 3) (𝓡 3) e (f y)).IsInvertible := by
      have hb := (G.embedding i).spatialMap_mfderiv_bijective
        (G.exhaustion_open i) hzero (hmem y hy)
      let L : EuclideanSpace ℝ (Fin 3) ≃L[ℝ] EuclideanSpace ℝ (Fin 3) :=
        ContinuousLinearEquiv.ofBijective (mfderiv (𝓡 3) (𝓡 3) e (f y))
          (LinearMap.ker_eq_bot.mpr hb.1) (LinearMap.range_eq_top.mpr hb.2)
      exact ⟨L, rfl⟩
    have hΦi : (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) Φ (c y)).IsInvertible :=
      ⟨Φ.mfderivToContinuousLinearEquiv (by simp) (c y), rfl⟩
    change (mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) (e ∘ f) y).IsInvertible
    rw [mfderiv_comp y ((he y hy).mdifferentiableAt (by simp))
      ((hf y).mdifferentiableAt (by simp))]
    apply hi.comp
    change (mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) (Φ ∘ c) y).IsInvertible
    rw [mfderiv_comp y (Φ.mdifferentiable (by simp) (c y))
      ((cylinderChart_symm_smooth q y).mdifferentiableAt (by simp))]
    exact hΦi.comp (cylinderChart_symm_isInvertible_mfderiv q y)

end PointedGeometricConvergence

end PoincareConjecture
