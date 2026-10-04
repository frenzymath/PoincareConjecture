import PoincareLib.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.Selection.Separation
import PoincareLib.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.EndCorrespondence
import PoincareLib.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.RicciComparison.SphereTransport

/-!
# Transporting the discarded side of a neck

A sphere homeomorphism fixing a common retained point sends the actual cut
tail to the actual cut tail. Compact support then preserves each original
terminal end. The fixed-accuracy neck comparison supplies this transport
when one neck center lies in the other carrier.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.SurgeryEndCut

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M} {N P : EpsilonNeck g}
  (C : SurgeryEndCut N) (D : SurgeryEndCut P)

theorem image_tail_eq_of_fixed_retained_point (e : M ≃ₜ M)
    (hsphere : e '' N.central_sphere = P.central_sphere) {p : M}
    (hpC : p ∈ connectedComponent N.center \ closure C.tail)
    (hpD : p ∈ connectedComponent P.center \ closure D.tail)
    (hfix : e p = p) : e '' C.tail = D.tail := by
  have hpS : p ∈ N.central_sphereᶜ := fun hs =>
    hpC.2 (frontier_subset_closure (C.frontier_eq.symm ▸ hs))
  have hcomp : e '' connectedComponent N.center = connectedComponent P.center := by
    rw [connectedComponent_eq hpC.1, connectedComponent_eq hpD.1]
    have hh := e.image_connectedComponentIn (s := univ) (x := p) (mem_univ p)
    simpa only [image_univ, e.surjective.range_eq, connectedComponentIn_univ, hfix] using hh
  have hret : e '' (connectedComponent N.center \ closure C.tail) =
      connectedComponent P.center \ closure D.tail := by
    rw [C.retained_eq_component hpC, D.retained_eq_component hpD,
      e.image_connectedComponentIn hpS, e.image_compl, hsphere, hfix]
  rw [C.tail_eq_component_diff_retained, image_sdiff e.injective, image_union,
    hcomp, hsphere, hret, ← D.tail_eq_component_diff_retained]

end PoincareMT.SurgeryEndCut

namespace PoincareMT.TerminalEnd

variable {G : GeneralizedRicciFlowData.{u}} {T : ℝ}
  {E : GeneralizedFlowExtension G T} {K : TerminalComponentPath E} (e : TerminalEnd K)

/-- A compactly supported sphere transport preserving the retained side
transfers a full original end from one actual surgery cut to another. -/
theorem exists_tail_subset_cut_of_supported_sphere_transport
    {N P : EpsilonNeck (E.extended.metric T)}
    (C : SurgeryEndCut N) (D : SurgeryEndCut P)
    (f : (E.extended.slice T).carrier ≃ₜ (E.extended.slice T).carrier)
    (hsphere : f '' N.central_sphere = P.central_sphere)
    {p : (E.extended.slice T).carrier}
    (hpC : p ∈ connectedComponent N.center \ closure C.tail)
    (hpD : p ∈ connectedComponent P.center \ closure D.tail)
    (hfixp : f p = p) {L : Set (E.extended.slice T).carrier}
    (hL : IsCompact L) (hfix : ∀ x, x ∉ L → f x = x)
    (n : ℕ) (htail : Subtype.val '' e.tail n ⊆ C.tail) :
    ∃ m, n ≤ m ∧ Subtype.val '' e.tail m ⊆ D.tail := by
  have heq := C.image_tail_eq_of_fixed_retained_point D f hsphere hpC hpD hfixp
  obtain ⟨k, hk⟩ := e.exists_tail_disjoint_compact hL
  refine ⟨max n k, le_max_left _ _, ?_⟩
  rintro x ⟨y, hy, rfl⟩
  have hxC := htail ⟨y, e.nested (le_max_left _ _) hy, rfl⟩
  have hxL : y.val ∉ L :=
    disjoint_left.mp (hk _ (le_max_right _ _)) ⟨y, hy, rfl⟩
  rw [← heq]
  exact ⟨y.val, hxC, hfix y.val hxL⟩

/-- At the original fixed accuracy, center containment transfers cut-end
coverage without replacing the selected neck or strengthening its accuracy. -/
theorem exists_tail_subset_cut_of_center_mem
    {N P : EpsilonNeck (E.extended.metric T)}
    (C : SurgeryEndCut N) (D : SurgeryEndCut P)
    (hN : N.epsilon ≤ 1 / 200) (hP : P.epsilon ≤ 1 / 200)
    (hcenter : P.center ∈ N.carrier)
    {p : (E.extended.slice T).carrier}
    (hpC : p ∈ connectedComponent N.center \ closure C.tail)
    (hpD : p ∈ connectedComponent P.center \ closure D.tail)
    (hpneck : p ∉ N.carrier ∪ P.carrier)
    (n : ℕ) (htail : Subtype.val '' e.tail n ⊆ C.tail) :
    ∃ m, n ≤ m ∧ Subtype.val '' e.tail m ⊆ D.tail := by
  obtain ⟨f, L, hL, hLN, hfix, hsphere⟩ :=
    P.central_sphere_smooth_transport_of_center_mem N hP hN hcenter
  apply e.exists_tail_subset_cut_of_supported_sphere_transport C D f.toHomeomorph
    hsphere hpC hpD (hfix p ?_) hL hfix n htail
  intro hpL
  rcases hLN hpL with hpP | hpN
  · exact hpneck (Or.inr hpP)
  · exact hpneck (Or.inl hpN)

end PoincareMT.TerminalEnd
