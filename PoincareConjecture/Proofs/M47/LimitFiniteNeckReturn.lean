import PoincareConjecture.Proofs.M47.LimitFiniteNeckDistances
import PoincareConjecture.Proofs.Horizon.Topology.Connected.BoundaryIncidence

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M47

theorem limitFinite_neck_return_impossible
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
    {g : RiemannianMetric 3 M} (N : EpsilonNeck g)
    {A : Set M} (hA : IsOpen A) (hfront : frontier A = N.central_sphere)
    {gamma : ℝ → M} {a s : ℝ} (hs : s ∈ Icc 0 a)
    (hcontinuous : ContinuousOn gamma (Icc 0 a))
    (hstart : gamma 0 = N.center)
    (hmin : ∀ u ∈ Icc 0 a, ∀ v ∈ Icc 0 a,
      g.edist (gamma u) (gamma v) = ENNReal.ofReal |u - v|)
    (hlength : 25 * N.scale ≤ s) (hin : gamma s ∈ A) (hout : gamma a ∉ A) :
    False := by
  have hsub : Icc s a ⊆ Icc 0 a := fun _ ht => ⟨hs.1.trans ht.1, ht.2⟩
  have hconnected : IsPreconnected (gamma '' Icc s a) :=
    isPreconnected_Icc.image gamma (hcontinuous.mono hsub)
  have hexists : ∃ v ∈ Icc s a, gamma v ∈ frontier A := by
    by_contra hnone
    have hdis : Disjoint (gamma '' Icc s a) (frontier A) := by
      rw [Set.disjoint_left]
      rintro _ ⟨v, hv, rfl⟩ hvfront
      exact hnone ⟨v, hv, hvfront⟩
    have hinside := Poincare.Topology.preconnected_subset_interior_of_disjoint_frontier
      hconnected hdis ⟨gamma s, ⟨s, ⟨le_rfl, hs.2⟩, rfl⟩,
        by simpa only [hA.interior_eq] using hin⟩
    exact hout (interior_subset (hinside ⟨a, ⟨hs.2, le_rfl⟩, rfl⟩))
  obtain ⟨v, hv, hvfront⟩ := hexists
  have hvsphere : gamma v ∈ N.central_sphere := hfront ▸ hvfront
  have hcenter := (N.mem_central_sphere_iff N.center).mp N.center_on_central_sphere
  have hvcenter := (N.mem_central_sphere_iff (gamma v)).mp hvsphere
  have hshort := limitFinite_same_height_distance N
    (N.central_sphere_subset N.center_on_central_sphere)
    (N.central_sphere_subset hvsphere) (hcenter.2.trans hvcenter.2.symm)
  have hvnonnegative : 0 ≤ v := hs.1.trans hv.1
  have hdistance := hmin 0 ⟨le_rfl, hs.1.trans hs.2⟩ v (hsub hv)
  rw [hstart, zero_sub, abs_neg, abs_of_nonneg hvnonnegative] at hdistance
  rw [hdistance, ENNReal.toReal_ofReal hvnonnegative] at hshort
  have hscale := N.scale_pos
  linarith [hv.1]

end PoincareConjecture.M47
