import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Positive.Regions.Basic
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.Reversal
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Chain.SmoothDomain













set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.NoncompactKappa.Positive

private theorem closure_side_eq_compl {X : Type*} [TopologicalSpace X]
    {A B S : Set X} (hB : IsOpen B) (hd : Disjoint A B)
    (hu : A ∪ B = Sᶜ) (hf : frontier A = S) : closure A = Bᶜ := by
  apply subset_antisymm (hd.closure_left hB).subset_compl_right
  intro x hx
  by_cases hxA : x ∈ A
  · exact subset_closure hxA
  · have hxS : x ∈ S := by
      by_contra hn
      have hab : x ∈ A ∪ B := hu ▸ hn
      exact hab.elim hxA hx
    exact frontier_subset_closure (hf ▸ hxS)

namespace SoulNeckRegion

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M}
  {S : RiemannianMetric.PointSoulData (K.flow.metric 0)} {epsilon D R : ℝ}
  (G : SoulNeckRegion K S epsilon D R)

theorem closure_inside_eq_compl_outside : closure G.inside = G.outsideᶜ :=
  closure_side_eq_compl G.outside_open G.disjoint G.complement_sphere G.inside_frontier

theorem closure_outside_eq_compl_inside : closure G.outside = G.insideᶜ :=
  closure_side_eq_compl G.inside_open G.disjoint.symm
    (union_comm G.outside G.inside |>.trans G.complement_sphere) G.outside_frontier

theorem interior_closure_inside : interior (closure G.inside) = G.inside := by
  rw [G.closure_inside_eq_compl_outside, interior_compl,
    G.closure_outside_eq_compl_inside, compl_compl]

theorem frontier_closure_inside : frontier (closure G.inside) =
    G.neck.terminal_neck.central_sphere := by
  calc
    frontier (closure G.inside) = closure G.inside \ G.inside := by
      rw [frontier, closure_closure, G.interior_closure_inside]
    _ = frontier G.inside := G.inside_open.frontier_eq.symm
    _ = G.neck.terminal_neck.central_sphere := G.inside_frontier



theorem exists_outward_neck :
    ∃ Q : EpsilonNeck (K.flow.metric 0), Q.epsilon = epsilon ∧
      Q.carrier = G.neck.terminal_neck.carrier ∧
      Q.central_sphere = G.neck.terminal_neck.central_sphere ∧
      Q.connection = K.flow.connection 0 ∧
      Q.scale = G.neck.terminal_neck.scale ∧
      Q.region (-Q.epsilon⁻¹) 0 ⊆ G.inside ∧
      Q.region 0 Q.epsilon⁻¹ ⊆ G.outside := by
  rcases G.sides with h | h
  · exact ⟨G.neck.terminal_neck, G.neck.terminal_epsilon, rfl, rfl,
      G.neck.terminal_connection, rfl,
      G.neck.terminal_epsilon.symm ▸ h.1, G.neck.terminal_epsilon.symm ▸ h.2⟩
  · refine ⟨G.neck.terminal_neck.reversed, G.neck.terminal_epsilon, rfl, rfl,
      G.neck.terminal_connection, rfl, ?_, ?_⟩
    · simpa only [EpsilonNeck.reversed_region, EpsilonNeck.reversed_epsilon,
        neg_zero, neg_neg, G.neck.terminal_epsilon] using h.2
    · simpa only [EpsilonNeck.reversed_region, EpsilonNeck.reversed_epsilon,
        neg_zero, G.neck.terminal_epsilon] using h.1


theorem exists_outward_height_neck :
    ∃ Q : EpsilonNeck (K.flow.metric 0),
      Q.epsilon = epsilon ∧
      Q.carrier = G.neck.terminal_neck.carrier ∧
      Q.central_sphere = G.neck.terminal_neck.central_sphere ∧
      Q.connection = K.flow.connection 0 ∧
      Q.scale = G.neck.terminal_neck.scale ∧
      ∀ y ∈ Q.carrier,
        y ∈ closure G.inside ↔ (Q.coordinate_inverse y).2 ≤ 0 := by
  obtain ⟨Q, hepsilon, hcarrier, hsphere, hconnection, hscale, hnegative, hpositive⟩ :=
    G.exists_outward_neck
  refine ⟨Q, hepsilon, hcarrier, hsphere, hconnection, hscale, ?_⟩
  intro y hy
  have hcoord := (Q.coordinate_inverse_mem y hy).2
  constructor
  · intro hinside
    by_contra hn
    have hout : y ∈ G.outside := hpositive ⟨hy, lt_of_not_ge hn, hcoord.2⟩
    exact (G.closure_inside_eq_compl_outside ▸ hinside) hout
  · intro hle
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact subset_closure (hnegative ⟨hy, hcoord.1, hlt⟩)
    · apply frontier_subset_closure
      rw [G.inside_frontier, ← hsphere]
      exact (Q.mem_central_sphere_iff y).mpr ⟨hy, heq⟩


theorem exists_closed_side_halfspace_chart (a : closure G.inside) :
    ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)),
      a.val ∈ e.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target ∧
      e.IsImage (closure G.inside) {y | 0 ≤ y 0} := by
  by_cases ha : a.val ∈ G.inside
  · obtain ⟨e, hae, he, hei, himg⟩ :=
      Poincare.Manifold.exists_interior_superlevel_halfspace_chart
        (E := EuclideanSpace ℝ (Fin 3)) (n := 2) (by simp)
        (f := fun _ : M => (1 : ℝ)) continuous_const 0 a.val (by norm_num)
    refine ⟨e.restrOpen G.inside G.inside_open, ⟨hae, ha⟩,
      he.mono (fun y hy => hy.1), hei.mono (fun y hy => hy.1), ?_⟩
    intro y hy
    exact iff_of_true ((himg hy.1).mpr (by norm_num)) (subset_closure hy.2)
  · obtain ⟨Q, _, _, hsphere, _, _, hheight⟩ := G.exists_outward_height_neck
    apply Q.exists_height_sublevel_halfspace_chart (t := 0) (K := closure G.inside)
    · apply Q.central_sphere_subset
      rw [hsphere, ← G.inside_frontier, G.inside_open.frontier_eq]
      exact ⟨a.property, ha⟩
    · exact hheight



theorem nonempty_smoothDomain : Nonempty (Poincare.Manifold.SmoothDomain 3 G.inside) := by
  obtain ⟨Q, _, _, hsphere, _, _, hheight⟩ := G.exists_outward_height_neck
  have hfront : frontier (closure G.inside) = Q.central_sphere :=
    G.frontier_closure_inside.trans hsphere.symm
  have hdomain := Q.nonempty_smoothDomain_of_height_sublevel G.compact_side
    (G.interior_closure_inside.symm ▸ G.inside_connected)
    (hfront ▸ Q.central_sphere_subset)
    (hfront ▸ ⟨Q.center, Q.center_on_central_sphere⟩) hheight
  simpa only [G.interior_closure_inside] using hdomain

end SoulNeckRegion

end PoincareConjecture.NoncompactKappa.Positive
