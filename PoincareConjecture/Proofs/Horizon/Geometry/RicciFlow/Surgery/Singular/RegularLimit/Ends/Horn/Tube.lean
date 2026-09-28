import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Ends.ProperHalf

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.TerminalEnd

variable {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
  {E : GeneralizedFlowExtension F T} {K : TerminalComponentPath E}

theorem exists_tube_closed_half_in_tail (e : TerminalEnd K)
    (A : RepairedNeckCapTopologyTheory.{u})
    {epsilon C B : ℝ} (hepsilon : 0 < epsilon) (hC : 0 < C)
    (hle : epsilon ≤ A.epsilon₀)
    (hlower : ∃ L : ℝ, ∀ x, L ≤ (E.extended.connection T).scalarCurvature x)
    (hproper : ∀ D : Set ℝ, IsCompact D →
      IsCompact ((E.extended.connection T).scalarCurvature ⁻¹' D))
    (hcanonical : ∀ x : (E.extended.slice T).carrier,
      B < (E.extended.connection T).scalarCurvature x →
        GeneralizedCanonicalControl (F := E.extended) T x epsilon C) (k : ℕ) :
    ∃ X : Set (E.extended.slice T).carrier,
      ∃ tube : EpsilonTubeCertificate (E.extended.metric T) X,
        tube.epsilon = epsilon ∧ ∃ side : Bool, ∃ a ∈ Ioo (0 : ℝ) 1,
          IsClosed (tube.cylinder.closedTail side a) ∧
          tube.cylinder.closedTail side a ⊆ Subtype.val '' e.tail k ∧
          ∀ b ∈ Ioo (0 : ℝ) 1, ∃ n : ℕ, ∀ m : ℕ, n ≤ m →
            Subtype.val '' e.tail m ⊆ tube.cylinder.tail side b := by
  have hR : Continuous (fun x : K.component =>
      (E.extended.connection T).scalarCurvature x) :=
    (E.extended.connection T).continuous_scalarCurvature.comp continuous_subtype_val
  obtain ⟨D, hD⟩ := (e.exhaustion.isCompact k).bddAbove_image hR.continuousOn
  obtain ⟨n₀, Y, hY, hfront, htail, _, hscalar, tube, htube⟩ :=
    e.exists_closed_tube_region A hepsilon hC hle hlower hproper hcanonical (D + 1)
  obtain ⟨side, a, ha, hclosure, hdir⟩ :=
    e.exists_cylinder_tail_closure_subset n₀ hY hfront htail tube
  let Q := tube.cylinder
  let b : ℝ := if side then (1 + a) / 2 else a / 2
  have hb : b ∈ Ioo (0 : ℝ) 1 := by
    cases side <;> dsimp [b] <;> constructor <;> linarith [ha.1, ha.2]
  have hab : if side then a < b else b < a := by
    cases side <;> dsimp [b] <;> linarith [ha.1, ha.2]
  have hlong : Q.tail side a ⊆ Y := subset_closure.trans hclosure
  have hhalfY : Q.closedTail side b ⊆ Y :=
    (Q.closedTail_subset_tail side ha hb hab).trans hlong
  have hclosed : IsClosed (Q.closedTail side b) :=
    Q.isClosed_closedTail_of_tail_subset side hY tube.contains_X ha hb hab hlong
  obtain ⟨n₁, _, hn₁⟩ := hdir b hb
  let n := max k n₁
  have hcapture : Subtype.val '' e.tail n ⊆ Q.closedTail side b :=
    (hn₁ n (le_max_right _ _)).trans (Q.tail_subset_closedTail side hb)
  have havoid : Disjoint (Q.closedTail side b)
      (Subtype.val '' (e.exhaustion k : Set K.component)) := by
    rw [Set.disjoint_left]
    rintro x hx ⟨z, hz, rfl⟩
    have hupper := hD ⟨z, hz, rfl⟩
    have hlower := hscalar z (hhalfY hx)
    linarith
  obtain ⟨x, hx⟩ := (e.tail_connected n).nonempty
  have hsub := e.subset_tail_image_of_isPreconnected k
    (Q.isConnected_closedTail side hb).isPreconnected havoid
    (e.nested (le_max_left k n₁) hx) (hcapture ⟨x, hx, rfl⟩)
  refine ⟨Y, tube, htube, side, b, hb, hclosed, hsub, ?_⟩
  intro c hc
  obtain ⟨n, _, hn⟩ := hdir c hc
  exact ⟨n, hn⟩

end PoincareConjecture.TerminalEnd
