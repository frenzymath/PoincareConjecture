import PoincareConjecture.Proofs.M76.Mathlib.SourcePoleQuadrantPatches
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLCirclePoleBranches

set_option autoImplicit false

open Set Geometry RectangleCornerArcs

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_source_pole_equator_labels
    {ψ : (ℝ × ℝ) → E} {F S g : Set E} {p q : E} {A : E →ₗ[ℝ] ℝ}
    {t r : ℝ} (hinj : Function.Injective ψ) (hψzero : ψ 0 = p) (hr : 0 < r)
    (hminus : SourcePoleQuadrantData ψ F S g p q A t (-r))
    (hplus : SourcePoleQuadrantData ψ F S g p q A t r)
    (arc : Bool × Bool → Set E)
    (hArc : ∀ i, IsFinitePLBallPair ℝ (arc i) {p, q}) (hpq : p ≠ q)
    (hArcInter : Pairwise (fun i j => arc i ∩ arc j = {p, q}))
    (hequator : arc (false, false) ∪ arc (false, true) = F ∩ {x | A x = 0}) :
    ∃ j : Bool,
      ψ '' ({0} ×ˢ uIcc 0 (-r)) ⊆ arc (false, j) ∧
      ψ '' ({0} ×ˢ uIcc 0 r) ⊆ arc (false, !j) := by
  let d : Bool → Set E := fun i => if i then ψ '' ({0} ×ˢ uIcc 0 r)
    else ψ '' ({0} ×ˢ uIcc 0 (-r))
  let c : Bool → E := fun i => ψ (0, if i then r else -r)
  have hd (i : Bool) : IsFinitePLBallPair ℝ (d i) {p, c i} := by
    cases i
    · exact hminus.vertical
    · exact hplus.vertical
  have hc (i : Bool) : c i ≠ p := by
    cases i
    · exact fun h => hminus.vertical_endpoint.2 (Or.inl h)
    · exact fun h => hplus.vertical_endpoint.2 (Or.inl h)
  have hcover (i : Bool) : d i ⊆ ⋃ j, arc (false, j) := by
    have hdF : d i ⊆ F ∩ {x | A x = 0} := by
      cases i
      · exact hminus.vertical_subset
      · exact hplus.vertical_subset
    intro x hx
    rcases hequator.symm.subset (hdF hx) with hleft | hright
    · exact mem_iUnion.mpr ⟨false, hleft⟩
    · exact mem_iUnion.mpr ⟨true, hright⟩
  have hmiss (i : Bool) : q ∉ d i := by
    cases i
    · exact hminus.vertical_other_notMem
    · exact hplus.vertical_other_notMem
  have hpair : Pairwise (fun i j => arc (false, i) ∩ arc (false, j) = {p, q}) := by
    intro i j hij
    exact hArcInter (fun h => hij (congrArg Prod.snd h))
  have hinter : d false ∩ d true = {p} :=
    (source_pole_opposite_axis_contacts hinj hψzero hr.le).1
  exact exists_opposite_circle_arc_labels (fun i => arc (false, i)) d c
    (fun i => hArc (false, i)) hpq hpair hd hc hcover hmiss hinter

theorem SourcePoleQuadrantData.attached_to_labelled_region
    {ψ : (ℝ × ℝ) → E} {F S g : Set E} {p q : E} {A : E →ₗ[ℝ] ℝ}
    {t z : ℝ} (h : SourcePoleQuadrantData ψ F S g p q A t z)
    (arc D : Bool × Bool → Set E)
    (hArc : Pairwise (fun i j => arc i ∩ arc j = {p, q}))
    (hD : ∀ i, IsFinitePLBallPair (ℝ × ℝ) (D i)
      (arc (false, i.2) ∪ arc (true, i.1)))
    (hcover : F ⊆ ⋃ i, D i) (hgraph : g = ⋃ i, arc i)
    (hpair : Pairwise (fun i j => D i ∩ D j ⊆ ⋃ k, arc k))
    (hcontact : ∀ i, D i ∩ (⋃ j, arc j) = arc (false, i.2) ∪ arc (true, i.1))
    (hlink : ∀ i : Bool, arc (true, i) =
      (F ∩ S) ∩ {x | if i then A x ≤ 0 else 0 ≤ A x})
    (hheight : A (ψ (t, 0)) = t) (k : Bool × Bool)
    (ht : if k.1 then t ≤ 0 else 0 ≤ t)
    (hz : ψ (0, z) ∈ arc (false, k.2)) :
    ψ '' (uIcc 0 t ×ˢ uIcc 0 z) ⊆ D k ∧
      ψ '' cornerArc 0 t 0 z ⊆ arc (false, k.2) ∪ arc (true, k.1) ∧
      (ψ '' cornerArc t 0 z 0) \ {ψ (0, z), ψ (t, 0)} ⊆
        D k \ (arc (false, k.2) ∪ arc (true, k.1)) := by
  have hgraphcontact : (ψ '' (uIcc 0 t ×ˢ uIcc 0 z)) ∩ (⋃ j, arc j) =
      ψ '' cornerArc 0 t 0 z := by
    rw [← hgraph]
    exact h.graph_contact
  have hhorizontal : ψ (t, 0) ∈ arc (true, k.1) := by
    apply (hlink k.1).symm.subset
    refine ⟨h.horizontal_subset h.horizontal_endpoint.1.1, ?_⟩
    change if k.1 then A (ψ (t, 0)) ≤ 0 else 0 ≤ A (ψ (t, 0))
    rwa [hheight]
  exact h.disk.attached_to_four_region_of_graph_contact arc D hArc
    (fun i => (hD i).isCompact.isClosed) (h.carrier_subset.trans hcover)
    hpair hcontact hgraphcontact h.corner_inter k
    ⟨ψ (0, z), ⟨(0, z), ⟨left_mem_uIcc, right_mem_uIcc⟩, rfl⟩,
      hz, h.vertical_endpoint.2⟩
    ⟨ψ (t, 0), ⟨(t, 0), ⟨right_mem_uIcc, left_mem_uIcc⟩, rfl⟩,
      hhorizontal, h.horizontal_endpoint.2⟩

end Geometry
