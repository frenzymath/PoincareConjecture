import PoincareLib.Geometry.Manifold.Immersion.AntipodalCollar
import PoincareLib.Geometry.Manifold.LocalDiffeomorph.Product
import PoincareLib.Geometry.RicciFlow.Compactness.Ancient.CompactEmbedding
import PoincareLib.Geometry.RicciFlow.Soliton.ThreeDimensional.Asymptotic.Curvature.SphereCover

/-!
# Antipodal exclusion through the stored ancient convergence maps

A compact cylinder slab lies in one exhaustion stage. At a later index with
a Euclidean source, its actual stored convergence map turns an antipodal
product cover into an impossible Euclidean collar local diffeomorphism.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareMT.AncientPointedGeometricConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t2Space FlowCarrier.t3Space

variable {S : ℕ → FlowCarrier.{0} 3} {g : ∀ k, ℝ → (S k).metric}
  {p : ∀ k, (S k).carrier} {T : ℝ}

/-- A local cylinder parametrization of the actual ancient limit cannot be
antipodally invariant when the actual subsequence sources are eventually
diffeomorphic to Euclidean three-space. -/
theorem not_antipodal_cylinderMap_of_eventually_euclidean
    (G : AncientPointedGeometricConvergence S g p T)
    (hE : ∀ᶠ i in atTop, Nonempty
      ((S (G.subsequence i)).carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ EuclideanSpace ℝ (Fin 3)))
    (Φ : RoundCylinderSpace → G.limitCarrier.carrier)
    (hΦ : IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ Φ) :
    ¬ ∀ q t, Φ (-q, t) = Φ (q, t) := by
  intro heven
  have hK : IsCompact (Φ '' (univ ×ˢ Icc (-1 : ℝ) 1)) :=
    (isCompact_univ.prod isCompact_Icc).image hΦ.contMDiff.continuous
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset hK
  obtain ⟨i, hji, ⟨d⟩⟩ := ((eventually_ge_atTop j).and hE).exists
  have hmono : Monotone G.exhaustion :=
    monotone_nat_of_le_succ G.exhaustion_increasing
  have hmem (z : RoundCylinderSpace) (hz : z ∈ univ ×ˢ Ioo (-1 : ℝ) 1) :
      Φ z ∈ G.exhaustion i :=
    hmono hji (hj (mem_image_of_mem Φ ⟨hz.1, hz.2.1.le, hz.2.2.le⟩))
  let F : RoundCylinderSpace → EuclideanSpace ℝ (Fin 3) :=
    d ∘ G.embedding i ∘ Φ
  apply Poincare.Manifold.not_isLocalDiffeomorphOn_antipodal_collar
    (a := 1) zero_lt_one F
  · intro q t _
    change d (G.embedding i (Φ (-q, t))) = d (G.embedding i (Φ (q, t)))
    rw [heven q t]
  · intro z
    have hemb := G.embedding_smooth i ⟨Φ z, hmem z z.property⟩
    exact ((hΦ z).comp (𝓡 3) _ hemb).comp (𝓡 3) _
      (d.isLocalDiffeomorph _)

variable {C : Type*} [TopologicalSpace C]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) C]

/-- An antipodal sphere cover of a product factor is incompatible with the
actual ancient convergence from eventual Euclidean sources. -/
theorem not_antipodal_cover_of_product_of_eventually_euclidean
    (G : AncientPointedGeometricConvergence S g p T)
    (hE : ∀ᶠ i in atTop, Nonempty
      ((S (G.subsequence i)).carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ EuclideanSpace ℝ (Fin 3)))
    (e : (C × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ G.limitCarrier.carrier)
    (q : UnitTwoSphere → C) (hq : IsLocalDiffeomorph (𝓡 2) (𝓡 2) ∞ q) :
    ¬ ∀ x, q (-x) = q x := by
  intro hqeven
  let Φ : RoundCylinderSpace → G.limitCarrier.carrier := e ∘ Prod.map q id
  have hprod : IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ))
      ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ (Prod.map q id) :=
    hq.prodMap (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞).isLocalDiffeomorph
  have hΦ : IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ Φ :=
    fun z => (hprod z).comp (𝓡 3) _ (e.isLocalDiffeomorph _)
  apply G.not_antipodal_cylinderMap_of_eventually_euclidean hE Φ hΦ
  intro x t
  change e (q (-x), t) = e (q x, t)
  rw [hqeven x]

variable [IsManifold (𝓡 2) ∞ C] [T2Space C] [T3Space C]
  [ConnectedSpace C] [CompactSpace C]

/-- For the retained round product limit, eventual Euclidean sources remove
the antipodal alternative and give exact centered normalized cylinder
coordinates on that same limit. -/
theorem exists_centered_scalarNormalized_roundCylinder_of_round_surface_product
    (G : AncientPointedGeometricConvergence S g p T)
    (hE : ∀ᶠ i in atTop, Nonempty
      ((S (G.subsequence i)).carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ EuclideanSpace ℝ (Fin 3)))
    (gC : RiemannianMetric 2 C) (D : LeviCivitaData gC)
    (hround : ConstantPositiveSectionalCurvature gC D)
    (e : (C × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ G.limitCarrier.carrier)
    (hmetric : ∀ (z : C × ℝ) (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z),
      (G.limitFlow.metric 0).inner (e z)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z v)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z w) =
          gC.inner z.1 v.1 w.1 + v.2 * w.2) :
    0 < (G.limitFlow.connection 0).scalarCurvature G.base ∧
      ∃ (Φ : RoundCylinderSpace ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ G.limitCarrier.carrier)
        (q : UnitTwoSphere), Φ (q, 0) = G.base ∧
        (fun z v w => (G.limitFlow.connection 0).scalarCurvature G.base *
          roundCylinderPullback (G.limitFlow.metric 0) Φ z v w) = EvolvingRoundCylinderMetric 0 := by
  obtain ⟨hR, hmodel | ⟨q, _, _, hlocal, _, hfibers⟩⟩ :=
    roundCylinder_or_antipodal_cover_of_round_surface_product gC (G.limitFlow.metric 0)
      D (G.limitFlow.connection 0) hround e hmetric G.base
  · exact ⟨hR, hmodel⟩
  · exact False.elim (G.not_antipodal_cover_of_product_of_eventually_euclidean hE e q hlocal
      (fun x => ((hfibers x (-x)).mpr (Or.inr rfl)).symm))

end PoincareMT.AncientPointedGeometricConvergence
