import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Ends.ClosedTube
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Ends.ClosedTails
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Ends.Cylinder.Smooth
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Ends.StrongNeckTails

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.TerminalEnd

variable {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
  {E : GeneralizedFlowExtension F T} {K : TerminalComponentPath E}

theorem exists_closed_half_in_tail (e : TerminalEnd K)
    (A : RepairedNeckCapTopologyTheory.{u})
    {epsilon C B : ℝ} (hepsilon : 0 < epsilon) (hC : 0 < C)
    (hle : epsilon ≤ A.epsilon₀)
    (hlower : ∃ L : ℝ, ∀ x, L ≤ (E.extended.connection T).scalarCurvature x)
    (hproper : ∀ D : Set ℝ, IsCompact D →
      IsCompact ((E.extended.connection T).scalarCurvature ⁻¹' D))
    (hcanonical : ∀ x : (E.extended.slice T).carrier,
      B < (E.extended.connection T).scalarCurvature x →
        GeneralizedCanonicalControl (F := E.extended) T x epsilon C) (k : ℕ) :
    ∃ U : Set (E.extended.slice T).carrier, ∃ Q : OpenCylinderModel U,
      IsOpen U ∧ ∃ side : Bool, ∃ a ∈ Ioo (0 : ℝ) 1,
        IsClosed (Q.closedTail side a) ∧
        Q.closedTail side a ⊆ Subtype.val '' e.tail k ∧
        ∃ n : ℕ, k ≤ n ∧ ∀ m : ℕ, n ≤ m →
          Subtype.val '' e.tail m ⊆ Q.closedTail side a := by
  have hR : Continuous (fun x : K.component =>
      (E.extended.connection T).scalarCurvature x) :=
    (E.extended.connection T).continuous_scalarCurvature.comp continuous_subtype_val
  obtain ⟨D, hD⟩ := (e.exhaustion.isCompact k).bddAbove_image hR.continuousOn
  obtain ⟨n₀, Y, hY, hfront, htail, _, hscalar, tube, _⟩ :=
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
  have hcapture : ∀ m : ℕ, n ≤ m → Subtype.val '' e.tail m ⊆ Q.closedTail side b := by
    intro m hm
    exact (hn₁ m ((le_max_right _ _).trans hm)).trans (Q.tail_subset_closedTail side hb)
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
    (e.nested (le_max_left k n₁) hx) (hcapture n le_rfl ⟨x, hx, rfl⟩)
  exact ⟨tube.carrier, Q, tube.carrier_open, side, b, hb,
    hclosed, hsub, n, le_max_left _ _, hcapture⟩

theorem exists_closed_strong_neck_half_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
        (E : GeneralizedFlowExtension F T) (K : TerminalComponentPath E)
        (e : TerminalEnd K) (A : RepairedNeckCapTopologyTheory.{u})
        {epsilon C B : ℝ},
        0 < epsilon → 0 < C → epsilon ≤ ε₀ → epsilon ≤ A.epsilon₀ →
        (∃ L : ℝ, ∀ x, L ≤ (E.extended.connection T).scalarCurvature x) →
        (∀ D : Set ℝ, IsCompact D →
          IsCompact ((E.extended.connection T).scalarCurvature ⁻¹' D)) →
        (∀ x : (E.extended.slice T).carrier,
          B < (E.extended.connection T).scalarCurvature x →
            GeneralizedCanonicalControl (F := E.extended) T x epsilon C) →
        ∃ U : Set (E.extended.slice T).carrier, ∃ Q : OpenCylinderModel U,
          IsOpen U ∧ ∃ side : Bool, ∃ a ∈ Ioo (0 : ℝ) 1,
            IsClosed (Q.closedTail side a) ∧ Q.closedTail side a ⊆ K.component ∧
            (∀ x ∈ Q.closedTail side a, ∃ N : TerminalStrongNeck E epsilon, N.center = x) ∧
            ∃ n : ℕ, Subtype.val '' e.tail n ⊆ Q.closedTail side a := by
  obtain ⟨ε₀, hε₀, hsmall, hneck⟩ := exists_strong_neck_tail_threshold.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro F T E K e A epsilon C B hepsilon hC hε hA hlower hproper hcanonical
  obtain ⟨k, hk⟩ := hneck E K e A hepsilon hC hε hA hlower hproper hcanonical
  obtain ⟨U, Q, hU, side, a, ha, hclosed, hsub, n, _, hn⟩ :=
    e.exists_closed_half_in_tail A hepsilon hC hA hlower hproper hcanonical k
  refine ⟨U, Q, hU, side, a, ha, hclosed, ?_, ?_, n, hn n le_rfl⟩
  · intro x hx
    obtain ⟨y, _, rfl⟩ := hsub hx
    exact y.property
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := hsub hx
    exact hk k le_rfl y hy

end PoincareConjecture.TerminalEnd
