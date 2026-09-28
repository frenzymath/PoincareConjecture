import PoincareConjecture.Definitions.Ch09.NeckCapTopology

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

attribute [local instance] SphereBundleCircleModel.carrier_topology
  SphereBundleCircleModel.carrier_charted SphereBundleCircleModel.carrier_manifold

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}

theorem SphereBundleCircleCertificate.exists_of_univ_model
    (B : SphereBundleCircleModel.{u})
    {epsilon : ℝ} (hepsilon_pos : 0 < epsilon)
    (hepsilon_cap : epsilon ≤ 1 / 200)
    (hconnected : IsConnected (Set.univ : Set M))
    (hcompact : IsCompact (Set.univ : Set M))
    (hcomponent : ∃ x : M, (Set.univ : Set M) = connectedComponent x)
    (e : (Set.univ : Set M) ≃ₜ B.carrier)
    (hforward : ContMDiffOn (𝓡 3) (𝓡 3) ∞
      (fun x : M => e ⟨x, mem_univ x⟩) (Set.univ : Set M))
    (hinverse : ContMDiff (𝓡 3) (𝓡 3) ∞
      (fun y : B.carrier => (e.symm y).1))
    (necks : Set (EpsilonNeck g))
    (hnecks : ∀ N ∈ necks, N.epsilon = epsilon)
    (hcover : (Set.univ : Set M) = ⋃ N : {N // N ∈ necks}, N.1.carrier)
    (hfiber : ∀ N ∈ necks, ∃ b : UnitCircle,
      SmoothSphereIsotopicIn (Set.univ : Set M) N.central_sphere
        {x : M | x ∈ (Set.univ : Set M) ∧
          B.projection (e ⟨x, mem_univ x⟩) = b}) :
    Nonempty (SphereBundleCircleCertificate g (Set.univ : Set M)) := by
  let forward : M → B.carrier := fun x => e ⟨x, mem_univ x⟩
  let inverse : B.carrier → M := fun y => (e.symm y).1
  refine ⟨{
    epsilon := epsilon
    epsilon_pos := hepsilon_pos
    epsilon_le_one_two_hundred := hepsilon_cap
    carrier := Set.univ
    contains_X := subset_rfl
    connected := hconnected
    compact := hcompact
    component := hcomponent
    model := B
    homeomorph := e
    forward := forward
    inverse := inverse
    forward_eq := ?_
    inverse_eq := ?_
    forward_smooth := ?_
    inverse_smooth := ?_
    necks := necks
    neck_epsilon := hnecks
    neck_cover := hcover
    fiber_isotopy := ?_ }⟩
  · intro x
    change e ⟨x.1, mem_univ x.1⟩ = e x
    congr 1
  · intro y
    rfl
  · simpa only [forward] using hforward
  · simpa only [inverse] using hinverse
  · intro N hN
    simpa only [forward] using hfiber N hN

end PoincareConjecture
