import PoincareConjecture.Proofs.Horizon.Topology.Manifold.ThreeDimensional.Triangulation.Embedded.Flags.EmbeddedThreeNormalFlags








set_option autoImplicit false

noncomputable section

open Set Metric
open scoped BigOperators Manifold ContDiff Topology NNReal

universe u v

namespace Poincare.Topology

theorem exists_finiteFlagComparison_preimage_on_hull
    {I : Type u} [PartialOrder I] [Fintype I]
    {E : Type v} [NormedAddCommGroup E] [NormedSpace Real E]
    (c d : I → E) (hinj : Function.Injective (finiteOrderComplexMap I c))
    (t : Finset I) (hchain : ∀ i ∈ t, ∀ j ∈ t, i ≤ j ∨ j ≤ i)
    (y : E) (hy : y ∈ convexHull Real (d '' (t : Set I))) :
    ∃ x ∈ convexHull Real (c '' (t : Set I)), finiteFlagComparison c d hinj x = y := by
  obtain ⟨w, hw, hzero, hsum, hval⟩ := exists_weights_of_mem_finite_hull_image d t y hy
  refine ⟨∑ i ∈ t, w i • c i, ?_, ?_⟩
  · rw [← Finset.centerMass_eq_of_sum_1 _ _ hsum]
    exact t.centerMass_mem_convexHull (fun i _ => hw i) (by rw [hsum]; exact zero_lt_one)
      (fun i hi => Set.mem_image_of_mem c hi)
  · exact (finiteFlagComparison_eq_sum c d hinj t hchain w hw hzero hsum).trans hval

namespace EmbeddedThreeFlagGrid

variable {N : Nat} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace Real (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {e : C(M, EuclideanSpace Real (Fin N))} {epsilon : NNReal}
  (G : EmbeddedThreeFlagGrid e epsilon)

theorem localManifoldFlag_range_subset (p : M) :
    Set.range (finiteOrderComplexMap (G.localFaces p) (G.localManifoldCenter p)) ⊆
      Set.range (finiteOrderComplexMap G.activeFaces G.activeCenter) := by
  classical
  intro y hy
  obtain ⟨t, ht, hchain, hyt⟩ :=
    (mem_range_finiteOrderComplexMap_iff (G.localManifoldCenter p) y).mp hy
  let inc (s : G.localFaces p) : G.activeFaces := ⟨s.val, s.property.1⟩
  apply (mem_range_finiteOrderComplexMap_iff G.activeCenter y).mpr
  refine ⟨t.image inc, ht.image inc, ?_, ?_⟩
  · intro i hi j hj
    obtain ⟨i', hi', rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨j', hj', rfl⟩ := Finset.mem_image.mp hj
    exact hchain i' hi' j' hj'
  · apply convexHull_mono _ hyt
    rintro _ ⟨i, hi, rfl⟩
    exact ⟨inc i, Finset.mem_image.mpr ⟨i, hi, rfl⟩, rfl⟩

theorem activeFlag_mem_ambient_face (y : EuclideanSpace Real (Fin N))
    (hy : y ∈ Set.range (finiteOrderComplexMap G.activeFaces G.activeCenter)) :
    ∃ s : G.activeFaces, y ∈ convexHull Real (s.val : Set (EuclideanSpace Real (Fin N))) := by
  obtain ⟨t, ht, hchain, hyt⟩ := (mem_range_finiteOrderComplexMap_iff G.activeCenter y).mp hy
  obtain ⟨s, hs, hsmax⟩ := Finset.exists_maximal ht
  refine ⟨s, ?_⟩
  apply convexHull_min _ (convex_convexHull Real _) hyt
  rintro _ ⟨i, hi, rfl⟩
  have his : i ≤ s := by
    rcases hchain i hi s hs with h | h
    · exact h
    · exact hsmax hi h
  exact convexHull_mono his (G.activeCenter_mem_hull i)

theorem localComparison_preimage_of_near (p : M)
    (y : EuclideanSpace Real (Fin N))
    (hy : y ∈ Set.range (finiteOrderComplexMap G.activeFaces G.activeCenter))
    (hnear : ‖y - e p‖ ≤ 2 * (N + 1 : Real) * G.h) :
    ∃ x : EuclideanSpace Real (Fin N),
      normalAffineConstraint (embeddedThreeTangent e p) (e p) x = 0 ∧
      ‖x - e p‖ ≤ 4 * (N + 1 : Real) * G.h ∧ G.localComparison p x = y := by
  classical
  let E := EuclideanSpace Real (Fin N)
  obtain ⟨t, ht, hchain, hyt⟩ := (mem_range_finiteOrderComplexMap_iff G.activeCenter y).mp hy
  obtain ⟨s, hs, hsmax⟩ := Finset.exists_maximal ht
  have hsub (i : G.activeFaces) (hi : i ∈ t) : i.val ⊆ s.val := by
    rcases hchain i hi s hs with h | h
    · exact h
    · exact hsmax hi h
  have hys : y ∈ convexHull Real (s.val : Set E) := by
    apply convexHull_min _ (convex_convexHull Real _) hyt
    rintro _ ⟨i, hi, rfl⟩
    exact convexHull_mono (hsub i hi) (G.activeCenter_mem_hull i)
  have hsize : ∀ x ∈ convexHull Real (s.val : Set E),
      ‖x - e p‖ ≤ 4 * (N + 1 : Real) * G.h := by
    intro x hx
    have hxy : ‖x - y‖ ≤ 2 * (N + 1 : Real) * G.h := by
      rw [← dist_eq_norm x y]
      exact (dist_le_diam_of_mem (s.val.finite_toSet.isCompact_convexHull Real).isBounded
        hx hys).trans (G.geometry s s.property.1).2.1
    have htri := dist_triangle x y (e p)
    rw [dist_eq_norm x (e p), dist_eq_norm x y, dist_eq_norm y (e p)] at htri
    linarith
  have hlocal (i : G.activeFaces) (hi : i ∈ t) : i.val ∈ G.localFaces p := by
    refine ⟨i.property, ?_⟩
    intro x hx
    have h := hsize x (convexHull_mono (hsub i hi) hx)
    have hpositive := mul_pos (show (0 : Real) < N + 1 by positivity) G.h_pos
    linarith
  let inc (i : G.localFaces p) : G.activeFaces := ⟨i.val, i.property.1⟩
  let t' : Finset (G.localFaces p) := Finset.univ.filter (fun i => inc i ∈ t)
  have ht' (i : G.localFaces p) : i ∈ t' ↔ inc i ∈ t := by
    simp only [t', Finset.mem_filter, Finset.mem_univ, true_and]
  have hchain' : ∀ i ∈ t', ∀ j ∈ t', i ≤ j ∨ j ≤ i := by
    intro i hi j hj
    exact hchain (inc i) ((ht' i).mp hi) (inc j) ((ht' j).mp hj)
  have hy' : y ∈ convexHull Real ((G.localManifoldCenter p) '' (t' : Set (G.localFaces p))) := by
    apply convexHull_mono _ hyt
    rintro _ ⟨i, hi, rfl⟩
    let j : G.localFaces p := ⟨i.val, hlocal i hi⟩
    refine ⟨j, (ht' j).mpr ?_, rfl⟩
    have heq : inc j = i := Subtype.ext rfl
    exact heq.symm ▸ hi
  obtain ⟨x, hxc, hxcomp⟩ := exists_finiteFlagComparison_preimage_on_hull
    (G.localTangentCenter p) (G.localManifoldCenter p) (G.localTangentFlag_injective p)
    t' hchain' y hy'
  refine ⟨x, ?_, ?_, hxcomp⟩
  · apply convexHull_min _
      ((convex_singleton (0 : (embeddedThreeTangent e p)ᗮ)).affine_preimage
        (normalAffineConstraint (embeddedThreeTangent e p) (e p))) hxc
    rintro _ ⟨i, _, rfl⟩
    exact (G.localTangentCenter_spec p i).1
  · apply hsize x
    apply convexHull_min _ (convex_convexHull Real _) hxc
    rintro _ ⟨i, hi, rfl⟩
    obtain ⟨w, hw, hsum, hval⟩ := G.localTangentCenter_weights p i
    apply convexHull_mono (hsub (inc i) ((ht' i).mp hi))
    exact Finset.mem_convexHull'.mpr ⟨w, fun v hv => (hw v hv).le, hsum, hval⟩

end EmbeddedThreeFlagGrid
end Poincare.Topology
