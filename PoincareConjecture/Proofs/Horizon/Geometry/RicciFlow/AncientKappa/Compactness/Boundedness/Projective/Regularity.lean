import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Projective.Cover
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Convergence.ParameterRegularity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Ancient.CompactEmbedding

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space
  normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

namespace PointedGeometricConvergence

theorem eventually_cylinderCover_parametrizations_regular
    {a b : ℝ} {S : PointedFlowSequence 3 a b}
    (G : PointedGeometricConvergence S) (hzero : a < 0 ∧ 0 < b)
    (Φ : RoundCylinderSpace → G.limitCarrier.carrier)
    (hΦ : IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ Φ)
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
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset (hcompact.image hΦ.contMDiff.continuous)
  filter_upwards [eventually_ge_atTop j] with i hji q
  let c : RoundCylinderCoordinates → RoundCylinderSpace :=
    fun y => ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm y.1, y.2)
  let f : RoundCylinderCoordinates → G.limitCarrier.carrier := Φ ∘ c
  let e : G.limitCarrier.carrier → (S.carrier (G.subsequence i)).carrier :=
    fun x => ((G.embedding i).toFun (0, x)).2
  let U := f ⁻¹' G.exhaustion j
  have hf : ContMDiff 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) ∞ f :=
    hΦ.contMDiff.comp (cylinderChart_symm_smooth q)
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
      ⟨(hΦ (c y)).mfderivToContinuousLinearEquiv (by simp), rfl⟩
    change (mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) (e ∘ f) y).IsInvertible
    rw [mfderiv_comp y ((he y hy).mdifferentiableAt (by simp))
      ((hf y).mdifferentiableAt (by simp))]
    apply hi.comp
    change (mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) (Φ ∘ c) y).IsInvertible
    rw [mfderiv_comp y (hΦ.mdifferentiable (by simp) (c y))
      ((cylinderChart_symm_smooth q y).mdifferentiableAt (by simp))]
    exact hΦi.comp (cylinderChart_symm_isInvertible_mfderiv q y)

end PointedGeometricConvergence

namespace AncientPointedGeometricConvergence

theorem eventually_cylinderCover_slab_regular
    {C : ℕ → FlowCarrier.{0} 3} {g : ∀ k, ℝ → (C k).metric}
    {p : ∀ k, (C k).carrier} {T : ℝ}
    (G : AncientPointedGeometricConvergence C g p T)
    (Φ : RoundCylinderSpace → G.limitCarrier.carrier)
    (hΦ : IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ Φ)
    (a b : ℝ) :
    ∀ᶠ i in atTop,
      IsLocalDiffeomorphOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
        (G.embedding i ∘ Φ) (univ ×ˢ Ioo a b) := by
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset
    ((isCompact_univ.prod (isCompact_Icc : IsCompact (Icc a b))).image
      hΦ.contMDiff.continuous)
  have hmono : Monotone G.exhaustion := monotone_nat_of_le_succ G.exhaustion_increasing
  filter_upwards [eventually_ge_atTop j] with i hji
  intro z
  have hz : Φ z ∈ G.exhaustion i := hmono hji
    (hj (mem_image_of_mem Φ ⟨mem_univ _, z.property.2.1.le, z.property.2.2.le⟩))
  exact (hΦ z).comp (𝓡 3) (C (G.subsequence i)).carrier
    (G.embedding_smooth i ⟨Φ z, hz⟩)

theorem eventually_cylinderCover_antipodal_fibers
    {C : ℕ → FlowCarrier.{0} 3} {g : ∀ k, ℝ → (C k).metric}
    {p : ∀ k, (C k).carrier} {T : ℝ}
    (G : AncientPointedGeometricConvergence C g p T)
    (Φ : RoundCylinderSpace → G.limitCarrier.carrier)
    (hΦ : Continuous Φ)
    (hfiber : ∀ z w, Φ z = Φ w ↔ w = z ∨ w = (-z.1, z.2))
    (a b : ℝ) :
    ∀ᶠ i in atTop, ∀ z ∈ univ ×ˢ Icc a b, ∀ w ∈ univ ×ˢ Icc a b,
      G.embedding i (Φ z) = G.embedding i (Φ w) ↔ w = z ∨ w = (-z.1, z.2) := by
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset
    ((isCompact_univ.prod (isCompact_Icc : IsCompact (Icc a b))).image hΦ)
  have hmono : Monotone G.exhaustion := monotone_nat_of_le_succ G.exhaustion_increasing
  filter_upwards [eventually_ge_atTop j] with i hji z hz w hw
  have hz' := hmono hji (hj (mem_image_of_mem Φ hz))
  have hw' := hmono hji (hj (mem_image_of_mem Φ hw))
  constructor
  · intro heq
    have heq' : (⟨Φ z, hz'⟩ : G.exhaustion i) = ⟨Φ w, hw'⟩ :=
      (G.embedding_open i).injective heq
    exact (hfiber z w).mp (congrArg Subtype.val heq')
  · intro h
    exact congrArg (G.embedding i) ((hfiber z w).mpr h)

end AncientPointedGeometricConvergence

end PoincareConjecture
