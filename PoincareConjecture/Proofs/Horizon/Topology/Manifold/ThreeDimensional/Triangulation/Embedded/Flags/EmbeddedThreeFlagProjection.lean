import PoincareConjecture.Proofs.Horizon.Topology.Manifold.ThreeDimensional.Triangulation.Embedded.Flags.EmbeddedThreeFlagLocalization
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.ThreeDimensional.Triangulation.Embedded.EmbeddedThreeNearest

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped BigOperators Manifold ContDiff Topology NNReal

universe u

namespace Poincare.Topology.EmbeddedThreeFlagGrid

variable {N : Nat} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace Real (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T2Space M] [CompactSpace M] [Nonempty M]
  {e : C(M, EuclideanSpace Real (Fin N))} {epsilon : NNReal}
  (G : EmbeddedThreeFlagGrid e epsilon)

omit [T2Space M] in
theorem activeFlag_nearest_distance (y : EuclideanSpace Real (Fin N))
    (hy : y ∈ Set.range (finiteOrderComplexMap G.activeFaces G.activeCenter)) :
    ‖y - e (embeddedThreeNearest e y)‖ ≤ 2 * (N + 1 : Real) * G.h := by
  obtain ⟨s, hys⟩ := G.activeFlag_mem_ambient_face y hy
  obtain ⟨q, hq⟩ := s.property.2
  rw [← dist_eq_norm y (e (embeddedThreeNearest e y))]
  exact (embeddedThreeNearest_minimal e y q).trans
    ((dist_le_diam_of_mem (s.val.finite_toSet.isCompact_convexHull Real).isBounded
      hys hq).trans (G.geometry s s.property.1).2.1)

set_option maxHeartbeats 3000000 in

def flagHomeomorphOfNearest
    (hs : ContMDiff (𝓡 3) (𝓘(Real, EuclideanSpace Real (Fin N))) ∞ e)
    (r : Real)
    (hc : ContinuousOn (embeddedThreeNearest e) {y | infDist y (Set.range e) < r})
    (hnormal : ∀ (p : M) (v : EuclideanSpace Real (Fin N)),
      v ∈ (embeddedThreeTangent e p)ᗮ → ‖v‖ < r →
        embeddedThreeNearest e (e p + v) = p)
    (hscale : 2 * (N + 1 : Real) * G.h < r)
    (kappa : NNReal) (hkappa : kappa < 1)
    (hcoefficient :
      96 * (N + 1 : Real) ^ 2 * (epsilon : Real) / ambientGridGap N (N - 4) *
        ((1 + (ambientGridGap N (N - 4) /
          (4 * (N + 1 : Real) * (2 : Real) ^ (N + 1)))⁻¹) ^ 4 - 1) ≤
            (kappa : Real)) :
    (finiteOrderComplex G.activeFaces).space ≃ₜ M := by
  let F := finiteOrderComplexMap G.activeFaces G.activeCenter
  let q : (finiteOrderComplex G.activeFaces).space → M := fun z => embeddedThreeNearest e (F z)
  have hnear (z : (finiteOrderComplex G.activeFaces).space) :
      infDist (F z) (Set.range e) < r := by
    have h := infDist_le_dist_of_mem (x := F z) (s := Set.range e)
      (Set.mem_range_self (embeddedThreeNearest e (F z)))
    rw [dist_eq_norm] at h
    exact (h.trans (G.activeFlag_nearest_distance (F z) (Set.mem_range_self z))).trans_lt hscale
  have hcont : Continuous q := hc.comp_continuous F.continuous hnear
  have hnormalq (z : (finiteOrderComplex G.activeFaces).space) :
      (embeddedThreeTangent e (q z)).orthogonalProjectionOnto (F z - e (q z)) = 0 :=
    (embeddedThreeTangent e (q z)).orthogonalProjectionOnto_eq_zero_iff.mpr
      (embedded_three_nearest_normal e hs (F z) (q z) (embeddedThreeNearest_minimal e (F z)))
  have hinj : Function.Injective q := by
    intro z z' hq
    let p := q z
    obtain ⟨y0, _, _, _, huniq⟩ := G.exists_local_normal_flag_point p kappa hkappa hcoefficient
    obtain ⟨x, hplane, hx, hFx⟩ := G.localComparison_preimage_of_near p (F z)
      (Set.mem_range_self z) (G.activeFlag_nearest_distance (F z) (Set.mem_range_self z))
    have hnear' : ‖F z' - e p‖ ≤ 2 * (N + 1 : Real) * G.h := by
      have h := G.activeFlag_nearest_distance (F z') (Set.mem_range_self z')
      change ‖F z' - e (q z')‖ ≤ _ at h
      rw [← hq] at h
      exact h
    obtain ⟨x', hplane', hx', hFx'⟩ := G.localComparison_preimage_of_near p (F z')
      (Set.mem_range_self z') hnear'
    have hzero : (embeddedThreeTangent e p).orthogonalProjectionOnto
        (G.localComparison p x - e p) = 0 := by
      rw [hFx]
      exact hnormalq z
    have hzero' : (embeddedThreeTangent e p).orthogonalProjectionOnto
        (G.localComparison p x' - e p) = 0 := by
      rw [hFx']
      have h := hnormalq z'
      rw [← hq] at h
      exact h
    have hy := huniq x hplane hx hzero
    have hy' := huniq x' hplane' hx' hzero'
    rw [hFx] at hy
    rw [hFx'] at hy'
    exact G.activeFlag_injective (hy.trans hy'.symm)
  have hsurj : Function.Surjective q := by
    intro p
    obtain ⟨y, hy, hdist, hproj, _⟩ := G.exists_local_normal_flag_point p kappa hkappa hcoefficient
    obtain ⟨z, hz⟩ := G.localManifoldFlag_range_subset p hy
    refine ⟨z, ?_⟩
    have hv : y - e p ∈ (embeddedThreeTangent e p)ᗮ :=
      (embeddedThreeTangent e p).orthogonalProjectionOnto_eq_zero_iff.mp hproj
    have heq := hnormal p (y - e p) hv (hdist.trans_lt hscale)
    change embeddedThreeNearest e (F z) = p
    rw [hz]
    simpa only [add_sub_cancel] using heq
  letI : CompactSpace (finiteOrderComplex G.activeFaces).space :=
    isCompact_iff_compactSpace.mp finiteOrderComplex_space_isCompact
  exact Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective q ⟨hinj, hsurj⟩) hcont

end Poincare.Topology.EmbeddedThreeFlagGrid
