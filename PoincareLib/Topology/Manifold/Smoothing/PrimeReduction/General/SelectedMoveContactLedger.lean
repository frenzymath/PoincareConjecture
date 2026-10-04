import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.General.SupportedMoveContactSet
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Simplicial.Mathlib.FiniteFaceCounts

/-!
# All-edge contact ledger after the selected move

The selected edge loses its two prescribed contacts, while every edge fixed
by the support keeps its cardinality.  This theorem packages those two
already-checked consequences into the family form consumed by the finite
Kneser induction.
-/

set_option autoImplicit false

open Set
open scoped BigOperators

namespace PoincareMT.M76

/-- Combine the selected-edge decrement with fixed-edge transport into one
finite edge-family ledger. -/
theorem ncard_edge_contact_family_after_selected_move
    {X ι : Type*} [TopologicalSpace X] [Fintype ι] [DecidableEq ι]
    (G : X ≃ₜ X) (edges : ι → Set X) (S : Set X) (selected : ι)
    (hfixed : ∀ i, i ≠ selected → EqOn G id (edges i))
    (hselected :
      (edges selected ∩ (G.symm '' S)).ncard =
        (edges selected ∩ S).ncard - 2) :
    ∀ i,
      (edges i ∩ (G.symm '' S)).ncard =
        if i = selected then (edges i ∩ S).ncard - 2
        else (edges i ∩ S).ncard := by
  intro i
  by_cases hi : i = selected
  · subst i
    simpa using hselected
  · simp only [hi, ↓reduceIte]
    exact ncard_inter_image_symm_eq_of_fixed G (hfixed i hi)

/-- The same ledger for the actual finite complex: a supported move whose
closed support misses every nonselected original edge fixes those edge
carriers pointwise, so the family conclusion is available directly on
`K.FaceOfCard 2`.  This is the concrete edge bookkeeping used by the
innermost reduction. -/
theorem ncard_face_edge_contact_family_after_selected_move
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace X] {K : Geometry.SimplicialComplex ℝ E}
    [Fintype (K.FaceOfCard 2)] [DecidableEq (K.FaceOfCard 2)] (g : E → X)
    (G : X ≃ₜ X) (C S : Set X)
    (selected : K.FaceOfCard 2)
    (hG : EqOn G id Cᶜ)
    (hdisj : ∀ a : K.FaceOfCard 2,
      a ≠ selected →
        Disjoint C (g '' convexHull ℝ (a.1 : Set E)))
    (hselected :
      ((g '' convexHull ℝ (selected.1 : Set E)) ∩ (G.symm '' S)).ncard =
        ((g '' convexHull ℝ (selected.1 : Set E)) ∩ S).ncard - 2) :
    ∀ a : K.FaceOfCard 2,
      ((g '' convexHull ℝ (a.1 : Set E)) ∩ (G.symm '' S)).ncard =
        if a = selected then
          (g '' convexHull ℝ (a.1 : Set E) ∩ S).ncard - 2
        else (g '' convexHull ℝ (a.1 : Set E) ∩ S).ncard := by
  apply ncard_edge_contact_family_after_selected_move G
    (fun a : K.FaceOfCard 2 =>
      g '' convexHull ℝ (a.1 : Set E)) S selected
  · intro a ha x hx
    apply hG
    intro hxC
    exact disjoint_left.mp (hdisj a ha) hxC hx
  · exact hselected

/-- The edge-family ledger lowers the total contact measure by two once the
selected edge contains the two distinct contacts removed by the move. -/
theorem sum_ncard_edge_contact_family_after_selected_move
    {X ι : Type*} [TopologicalSpace X] [Fintype ι] [DecidableEq ι]
    (G : X ≃ₜ X) (edges : ι → Set X) (S : Set X) (selected : ι)
    (hfixed : ∀ i, i ≠ selected → EqOn G id (edges i))
    (hselected :
      (edges selected ∩ (G.symm '' S)).ncard =
        (edges selected ∩ S).ncard - 2)
    (hcount : 2 ≤ (edges selected ∩ S).ncard) :
    (∑ i, (edges i ∩ (G.symm '' S)).ncard) =
      (∑ i, (edges i ∩ S).ncard) - 2 := by
  classical
  let f : ι → ℕ := fun i => (edges i ∩ S).ncard
  let g : ι → ℕ := fun i => (edges i ∩ (G.symm '' S)).ncard
  have hledger : ∀ i, g i = if i = selected then f i - 2 else f i := by
    intro i
    exact ncard_edge_contact_family_after_selected_move G edges S selected
      hfixed hselected i
  have hcount' : 2 ≤ f selected := by
    simpa [f] using hcount
  have hnew : (∑ i, g i) =
      (∑ i ∈ Finset.univ.erase selected, f i) + (f selected - 2) := by
    rw [← Finset.sum_erase_add Finset.univ g (Finset.mem_univ selected)]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      rw [hledger i]
      simp [Finset.mem_erase.mp hi]
  have hold : (∑ i, f i) =
      (∑ i ∈ Finset.univ.erase selected, f i) + f selected := by
    symm
    exact Finset.sum_erase_add Finset.univ f (Finset.mem_univ selected)
  rw [hnew, hold]
  omega

/-! A producer may expose cardinality preservation for untouched edges without
an explicit pointwise fixation certificate. -/

theorem sum_ncard_edge_contact_family_after_counted_move
    {X ι : Type*} [TopologicalSpace X] [Fintype ι] [DecidableEq ι]
    (G : X ≃ₜ X) (edges : ι → Set X) (S : Set X) (selected : ι)
    (hfixed : ∀ i, i ≠ selected →
      (edges i ∩ (G.symm '' S)).ncard = (edges i ∩ S).ncard)
    (hselected :
      (edges selected ∩ (G.symm '' S)).ncard =
        (edges selected ∩ S).ncard - 2)
    (hcount : 2 ≤ (edges selected ∩ S).ncard) :
    (∑ i, (edges i ∩ (G.symm '' S)).ncard) =
      (∑ i, (edges i ∩ S).ncard) - 2 := by
  classical
  let f : ι → ℕ := fun i => (edges i ∩ S).ncard
  let g : ι → ℕ := fun i => (edges i ∩ (G.symm '' S)).ncard
  have hledger : ∀ i, g i = if i = selected then f i - 2 else f i := by
    intro i
    by_cases hi : i = selected
    · subst i
      simpa [f, g] using hselected
    · simp only [hi, ↓reduceIte]
      exact hfixed i hi
  have hcount' : 2 ≤ f selected := by
    simpa [f] using hcount
  have hnew : (∑ i, g i) =
      (∑ i ∈ Finset.univ.erase selected, f i) + (f selected - 2) := by
    rw [← Finset.sum_erase_add Finset.univ g (Finset.mem_univ selected)]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      rw [hledger i]
      simp [Finset.mem_erase.mp hi]
  have hold : (∑ i, f i) =
      (∑ i ∈ Finset.univ.erase selected, f i) + f selected := by
    symm
    exact Finset.sum_erase_add Finset.univ f (Finset.mem_univ selected)
  rw [hnew, hold]
  omega

/-- Consume the complete supported-move set equations in the finite family
ledger.  The two-contact equation itself supplies the lower bound needed by
the total-measure subtraction, so a later innermost producer only has to
construct the geometric move and its exact retained-edge contact equation. -/
theorem sum_ncard_edge_contact_family_after_supported_move
    {X ι : Type*} [TopologicalSpace X] [Fintype ι] [DecidableEq ι]
    (G : X ≃ₜ X) (edges : ι → Set X) (S : Set X) (selected : ι)
    (e w W : Set X) {u v : X}
    (hedges : edges selected = e)
    (hfixed : ∀ i, i ≠ selected → EqOn G id (edges i))
    (hedge : G '' e = (e \ w) ∪ W)
    (hfix : EqOn G id (e \ w))
    (hdisj : Disjoint W S)
    (hcontact : (e \ w) ∩ S = (e ∩ S) \ ({u, v} : Set X))
    (hfin : (e ∩ S).Finite)
    (hu : u ∈ e ∩ S) (hv : v ∈ e ∩ S) (huv : u ≠ v) :
    (∑ i, (edges i ∩ (G.symm '' S)).ncard) =
      (∑ i, (edges i ∩ S).ncard) - 2 := by
  have hdrop :
      (e ∩ (G.symm '' S)).ncard = (e ∩ S).ncard - 2 :=
    ncard_inter_image_symm_eq_sub_two G hedge hfix hdisj hcontact hfin hu hv huv
  have hselected :
      (edges selected ∩ (G.symm '' S)).ncard =
        (edges selected ∩ S).ncard - 2 := by
    simpa [hedges] using hdrop
  have hpair : ({u, v} : Set X) ⊆ e ∩ S := by
    intro x hx
    rcases hx with rfl | rfl
    · exact hu
    · exact hv
  have hpaircard : ({u, v} : Set X).ncard = 2 := ncard_pair huv
  have hcount : 2 ≤ (e ∩ S).ncard := by
    have hle : ({u, v} : Set X).ncard ≤ (e ∩ S).ncard :=
      Set.ncard_le_ncard hpair hfin
    omega
  apply sum_ncard_edge_contact_family_after_selected_move G edges S selected
    hfixed hselected
  simpa [hedges] using hcount

end PoincareMT.M76
