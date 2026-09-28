import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CutTopology
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Geometry.EndCut.Topology.Components
import PoincareConjecture.Proofs.Horizon.Topology.Connected.BoundaryIncidence








set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.SurgeryEndCut

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M} {N : EpsilonNeck g} (C : SurgeryEndCut N)

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] in
theorem tail_isConnected : IsConnected C.tail := by
  rw [C.component_eq]
  exact isConnected_connectedComponentIn_iff.mpr
    (connectedComponentIn_subset _ _ (C.component_eq ▸ C.positive_subset C.point_positive))

theorem tail_subset_component : C.tail ⊆ connectedComponent N.center := by
  rw [connectedComponent_eq (N.carrier_subset_connectedComponent C.point_positive.1)]
  exact C.tail_isConnected.subset_connectedComponent (C.positive_subset C.point_positive)

include C in
theorem isSeparating : N.IsSeparating := by
  refine ⟨N.component_diff_central_sphere_nonempty, ?_⟩
  intro hconn
  have hi := inv_pos.mpr N.epsilon_pos
  obtain ⟨p, hp⟩ := (N.isConnected_region le_rfl hi.le (neg_lt_zero.mpr hi)).nonempty
  have hpS : p ∉ N.central_sphere := by
    intro hs
    have hz := ((N.mem_central_sphere_iff p).mp hs).2
    exact (ne_of_lt hp.2.2) hz
  have hqS : C.point ∉ N.central_sphere :=
    disjoint_left.mp C.tail_disjoint_central (C.positive_subset C.point_positive)
  have hsub := hconn.isPreconnected.subset_connectedComponentIn
    (show C.point ∈ connectedComponent N.center \ N.central_sphere from
      ⟨N.carrier_subset_connectedComponent C.point_positive.1, hqS⟩)
    (show connectedComponent N.center \ N.central_sphere ⊆ N.central_sphereᶜ from
      fun _ hx => hx.2)
  exact disjoint_left.mp C.negative_disjoint hp
    (C.component_eq.symm ▸ hsub ⟨N.carrier_subset_connectedComponent hp.1, hpS⟩)

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] in
private theorem eq_component_of_frontier {A S : Set M} (hA : IsOpen A)
    (hc : IsConnected A) (hf : frontier A = S) {p : M} (hp : p ∈ A) :
    A = connectedComponentIn Sᶜ p := by
  have hAS : A ⊆ Sᶜ := fun _ hx hs => (hf.symm ▸ hs).2 (hA.interior_eq.symm ▸ hx)
  apply Subset.antisymm (hc.isPreconnected.subset_connectedComponentIn hp hAS)
  apply (Poincare.Topology.preconnected_subset_interior_of_disjoint_frontier
    isPreconnected_connectedComponentIn ?_ ?_).trans interior_subset
  · exact disjoint_left.mpr fun _ hx hs => connectedComponentIn_subset _ _ hx (hf ▸ hs)
  · exact ⟨p, mem_connectedComponentIn (hAS hp), hA.interior_eq.symm ▸ hp⟩


theorem retained_isConnected :
    IsConnected (connectedComponent N.center \ closure C.tail) := by
  obtain ⟨A, B, hAo, hBo, hAc, hBc, hdis, hab, hfA, hfB, _⟩ :=
    N.exists_exhaustive_complementary_regions C.isSeparating
  have hq : C.point ∈ A ∪ B := by
    rw [hab]
    exact ⟨N.carrier_subset_connectedComponent C.point_positive.1,
      disjoint_left.mp C.tail_disjoint_central (C.positive_subset C.point_positive)⟩
  rcases hq with hq | hq
  · have heq : A = C.tail :=
      (eq_component_of_frontier hAo hAc hfA hq).trans C.component_eq.symm
    have hret : connectedComponent N.center \ closure C.tail = B := by
      rw [C.closure_tail, ← heq]
      ext x
      have hh := Set.ext_iff.mp hab x
      have hd : x ∈ A → x ∈ B → False := fun ha hb => Set.disjoint_left.mp hdis ha hb
      simp only [mem_sdiff, mem_union] at hh ⊢
      constructor
      · intro hx
        exact (hh.mpr ⟨hx.1, fun hs => hx.2 (Or.inr hs)⟩).resolve_left
          (fun ha => hx.2 (Or.inl ha))
      · intro hx
        exact ⟨(hh.mp (Or.inr hx)).1, fun h => h.elim (fun ha => hd ha hx)
          (hh.mp (Or.inr hx)).2⟩
    exact hret.symm ▸ hBc
  · have heq : B = C.tail :=
      (eq_component_of_frontier hBo hBc hfB hq).trans C.component_eq.symm
    have hret : connectedComponent N.center \ closure C.tail = A := by
      rw [C.closure_tail, ← heq]
      ext x
      have hh := Set.ext_iff.mp hab x
      have hd : x ∈ A → x ∈ B → False := fun ha hb => Set.disjoint_left.mp hdis ha hb
      simp only [mem_sdiff, mem_union] at hh ⊢
      constructor
      · intro hx
        exact (hh.mpr ⟨hx.1, fun hs => hx.2 (Or.inr hs)⟩).resolve_right
          (fun hb => hx.2 (Or.inl hb))
      · intro hx
        exact ⟨(hh.mp (Or.inl hx)).1, fun h => h.elim (hd hx)
          (hh.mp (Or.inl hx)).2⟩
    exact hret.symm ▸ hAc


theorem retained_eq_component {p : M}
    (hp : p ∈ connectedComponent N.center \ closure C.tail) :
    connectedComponent N.center \ closure C.tail =
      connectedComponentIn N.central_sphereᶜ p := by
  have hsub : connectedComponent N.center \ closure C.tail ⊆ N.central_sphereᶜ := by
    intro x hx hs
    exact hx.2 (frontier_subset_closure (C.frontier_eq.symm ▸ hs))
  apply Subset.antisymm
    (C.retained_isConnected.isPreconnected.subset_connectedComponentIn hp hsub)
  intro x hx
  have hcomponent : x ∈ connectedComponent N.center := by
    have hh := isPreconnected_connectedComponentIn.subset_connectedComponent
      (mem_connectedComponentIn (hsub hp)) hx
    rwa [← connectedComponent_eq hp.1] at hh
  refine ⟨hcomponent, ?_⟩
  have havoid : Disjoint (connectedComponentIn N.central_sphereᶜ p) (frontier C.tail) := by
    rw [C.frontier_eq]
    exact disjoint_left.mpr fun _ hy => connectedComponentIn_subset _ _ hy
  have hout := Poincare.Topology.preconnected_subset_interior_of_disjoint_frontier
    isPreconnected_connectedComponentIn (D := C.tailᶜ)
    (by simpa only [frontier_compl] using havoid)
    (show (connectedComponentIn N.central_sphereᶜ p ∩ interior C.tailᶜ).Nonempty from
      ⟨p, mem_connectedComponentIn (hsub hp), by
        simpa only [interior_compl, mem_compl_iff] using hp.2⟩)
  simpa only [interior_compl, mem_compl_iff] using hout hx

theorem tail_eq_component_diff_retained :
    C.tail = connectedComponent N.center \
      (N.central_sphere ∪ (connectedComponent N.center \ closure C.tail)) := by
  classical
  ext x
  rw [C.closure_tail]
  have hcomp : x ∈ C.tail → x ∈ connectedComponent N.center :=
    fun hx => C.tail_subset_component hx
  have hdis : x ∈ C.tail → x ∉ N.central_sphere :=
    fun hx => disjoint_left.mp C.tail_disjoint_central hx
  simp only [mem_sdiff, mem_union]
  tauto

end PoincareConjecture.SurgeryEndCut
