import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Cuts.CountZeroSelection
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Attachments.SquareCollars



set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "Band" => squareAnnulus 1 (1 / 8)
local notation "Ann" => squareAnnulus 8 1

open Classical in
theorem exists_attached_selected_cut_annulus
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : SimplicialComplex ℝ E) (N M : Bool → Set E)
    (c : ∀ b, Band ≃ₜ N b) (hc : ∀ b, (c b).IsFinitePL)
    (hdisN : Disjoint (N false) (N true)) (hMN : ∀ b, M b ⊆ N b)
    (hcore : ∀ b x, (c b x : E) ∈ M b ↔ depth 1 x = 0)
    (hcut : ∀ b x, (c b x : E) ∈ K.space ↔
      depth 1 x = -(1 / 8 : ℝ) ∨ depth 1 x = 1 / 8)
    (B : Bool × Bool → SimplicialComplex ℝ E)
    (hBN : ∀ i, (B i).space ⊆ N i.1)
    (hlevel : ∀ i x, (c i.1 x : E) ∈ (B i).space ↔
      depth 1 x = if i.2 then (1 / 8 : ℝ) else -(1 / 8 : ℝ))
    (r : Bool → Bool → K.vertexAbstractComplex.edgeGraph.ConnectedComponent)
    (D : K.vertexAbstractComplex.edgeGraph.ConnectedComponent) (s t : Bool)
    (hr : ∀ b u, B (b, u) ≤ K.edgeComponentComplex (r b u))
    (hselected : componentRims r D = {(false, s), (true, t)})
    (H : Ann ≃ₜ (K.edgeComponentComplex D).space) (hH : H.IsFinitePL)
    (hH0 : ∀ x, (H x : E) ∈ (B (false, s)).space ↔ depth 8 x = -1)
    (hH1 : ∀ x, (H x : E) ∈ (B (true, t)).space ↔ depth 8 x = 1) :
    ∃ (T : Set E) (F : Ann ≃ₜ T), F.IsFinitePL ∧
      T ⊆ (N false ∪ K.space) ∪ N true ∧
      M false ⊆ T ∧ M true ⊆ T ∧
      (∀ x, (F x : E) ∈ M false ↔ depth 8 x = -1) ∧
      ∀ x, (F x : E) ∈ M true ↔ depth 8 x = 1 := by
  classical
  let side : Bool → Bool := fun b ↦ if b then t else s
  have hri (b u : Bool) : r b u = D ↔ u = side b := by
    have H : r b u = D ↔ (b, u) = (false, s) ∨ (b, u) = (true, t) := by
      have hm : (b, u) ∈ componentRims r D ↔
          (b, u) = (false, s) ∨ (b, u) = (true, t) := by
        rw [hselected, Finset.mem_insert, Finset.mem_singleton]
      simpa only [componentRims, Finset.mem_filter, Finset.mem_univ, true_and] using hm
    cases b <;> simpa [side] using H
  have hcin (b : Bool) (x : Band) :
      (c b x : E) ∈ (K.edgeComponentComplex D).space ↔
        depth 1 x = if side b then (1 / 8 : ℝ) else -(1 / 8 : ℝ) := by
    constructor
    · intro hx
      have hxK := SimplicialComplex.space_subset_of_le (K.edgeComponentComplex_le D) hx
      have H (u : Bool) (hu : depth 1 x = if u then (1 / 8 : ℝ) else -(1 / 8 : ℝ)) :
          depth 1 x = if side b then (1 / 8 : ℝ) else -(1 / 8 : ℝ) := by
        have hxB := (hlevel (b, u) x).mpr hu
        have hrD := (mem_component_of_assigned_rim_iff K (B (b, u)) (r b u) D
          (hr b u) hxB).mp hx
        exact (hri b u).mp hrD ▸ hu
      exact ((hcut b x).mp hxK).elim (H false) (H true)
    · intro hd
      have hxB := (hlevel (b, side b) x).mpr hd
      exact (mem_component_of_assigned_rim_iff K (B (b, side b)) (r b (side b)) D
        (hr b (side b)) hxB).mpr ((hri b (side b)).mpr rfl)
  have hHmem (b : Bool) (x : Ann) :
      (H x : E) ∈ N b ↔ (H x : E) ∈ (B (b, side b)).space := by
    constructor
    · intro hx
      let p := (c b).symm ⟨H x, hx⟩
      have hp : (c b p : E) = H x := congrArg Subtype.val ((c b).apply_symm_apply _)
      have hd := (hcin b p).mp (hp ▸ (H x).property)
      exact hp ▸ (hlevel (b, side b) p).mpr hd
    · exact fun hx ↦ hBN (b, side b) hx
  let σ : ℝ := if s then 1 else -1
  let τ : ℝ := if t then 1 else -1
  obtain ⟨T, F, hF, _, hFT, hM0, hM1, hF0, hF1⟩ :=
    exists_marked_square_collar_attachment (c false) H (c true)
      (hc false) hH (hc true) hdisN σ τ
      (by cases s <;> simp [σ]) (by cases t <;> simp [τ])
      (by intro x; simpa only [side, Bool.false_eq_true, ite_false, σ, ite_div, neg_div] using hcin false x)
      (fun x ↦ (hHmem false x).trans (hH0 x))
      (fun x ↦ (hHmem true x).trans (hH1 x))
      (by intro x; simpa only [side, ite_true, τ, ite_div, neg_div] using hcin true x)
      (hMN false) (hMN true) (hcore false) (hcore true)
  refine ⟨T, F, hF, hFT.trans ?_, hM0, hM1, hF0, hF1⟩
  exact union_subset_union_left _ (union_subset_union_right _
    (SimplicialComplex.space_subset_of_le (K.edgeComponentComplex_le D)))

end PoincareConjecture.M76.Dehn.Annuli
