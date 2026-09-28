import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Compactness

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.AncientCompactTimeConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t3Space FlowCarrier.secondCountable

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution n M} {S : AncientRescalingSequence K}

theorem eventually_exhaustion_eq_univ (G : AncientCompactTimeConvergence S)
    (hcompact : CompactSpace G.limit.carrier.carrier) :
    ∀ᶠ k in atTop, G.exhaustion k = univ := by
  let : CompactSpace G.limit.carrier.carrier := hcompact
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset isCompact_univ
  have hmono : Monotone G.exhaustion := monotone_nat_of_le_succ G.exhaustion_increasing
  filter_upwards [eventually_ge_atTop j] with k hk
  exact eq_univ_of_univ_subset (hj.trans (hmono hk))

theorem exists_spatialDiffeomorph_of_exhaustion_eq_univ
    (G : AncientCompactTimeConvergence S) (hcompact : CompactSpace G.limit.carrier.carrier)
    (k : ℕ) (hk : G.exhaustion k = univ) {t : ℝ}
    (ht : t ∈ ancientM18TimeWindow k) :
    ∃ φ : G.limit.carrier.carrier ≃ₘ⟮𝓡 n, 𝓡 n⟯ M,
      ∀ x, φ x = ((G.embedding k).toFun (t, x)).2 := by
  let : CompactSpace G.limit.carrier.carrier := hcompact
  let f : G.limit.carrier.carrier → M := fun x => ((G.embedding k).toFun (t, x)).2
  have hmem (x : G.limit.carrier.carrier) : x ∈ G.exhaustion k := hk ▸ mem_univ x
  have hf : ContMDiff (𝓡 n) (𝓡 n) ∞ f := fun x =>
    (G.embedding k).spatialMap_contMDiffAt (G.exhaustion_open k) ht (hmem x)
  have hderiv : ∀ x, Function.Bijective (mfderiv (𝓡 n) (𝓡 n) f x) := fun x =>
    (G.embedding k).spatialMap_mfderiv_bijective (G.exhaustion_open k) ht (hmem x)
  have hlocal := Poincare.isLocalDiffeomorph_of_contMDiff_bijective_mfderiv hf hderiv
  have hinj : Function.Injective f := by
    intro x y hxy
    have hpair : (G.embedding k).toFun (t, x) = (G.embedding k).toFun (t, y) := by
      apply Prod.ext
      · rw [(G.embedding k).time_preserving, (G.embedding k).time_preserving]
      · exact hxy
    exact congrArg Prod.snd ((G.embedding k).injective_on ⟨ht, hmem x⟩
      ⟨ht, hmem y⟩ hpair)
  have hc : IsCompact (range f) := by simpa using isCompact_univ.image hf.continuous
  have hu : range f = univ :=
    (show IsClopen (range f) from ⟨hc.isClosed, hlocal.isOpenMap.isOpen_range⟩).eq_univ
      ⟨f G.limit.base, mem_range_self G.limit.base⟩
  have hsurj : Function.Surjective f := range_eq_univ.mp hu
  exact ⟨hlocal.diffeomorphOfBijective ⟨hinj, hsurj⟩, fun _ => rfl⟩

theorem eventually_exists_spatialDiffeomorph
    (G : AncientCompactTimeConvergence S) (hcompact : CompactSpace G.limit.carrier.carrier) :
    ∀ᶠ k in atTop, ∃ φ : G.limit.carrier.carrier ≃ₘ⟮𝓡 n, 𝓡 n⟯ M,
      ∀ x, φ x = ((G.embedding k).toFun (-1, x)).2 := by
  filter_upwards [G.eventually_exhaustion_eq_univ hcompact] with k hk
  exact G.exists_spatialDiffeomorph_of_exhaustion_eq_univ hcompact k hk (G.time_window_base k)

end PoincareConjecture.AncientCompactTimeConvergence
