import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Disks.FinitePLFourDiskGluing
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Coordinates.CoordinateFourRegionIncidence

/-!
# Relabel the original equator using its actual inside

One common geometric inside label at the two poles reindexes
only the equator arcs and the second disk index. All original
carriers, graph contacts and numerical height data are retained.
See Alexander 1924, pp. 6--8, Hudson 1969, pp. 15--19 and
M76 derivation 301.
-/

set_option autoImplicit false

open Set CoordinateFourRegions

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A common inside equator label gives the literal signed
axis labels at both poles, retaining the complete original
graph, all disk contacts, and each numerical height union.
The two original surface-link arcs are unchanged. The common
label is supplied by geometry before this reindexing.
See Alexander pp. 6--8 and M76 derivation 301. -/
theorem exists_marked_graph_with_signed_vertical_labels
    {F S : Set E} (arc disk : Bool × Bool → Set E) (a b : E) (A : E → ℝ)
    (hArc : ∀ i, IsFinitePLBallPair ℝ (arc i) {a, b})
    (hArcInter : Pairwise (fun i j => arc i ∩ arc j = {a, b}))
    (hDisk : ∀ i, IsFinitePLBallPair (ℝ × ℝ) (disk i)
      (arc (false, i.2) ∪ arc (true, i.1)))
    (hcontact : ∀ i, disk i ∩ (⋃ k, arc k) = arc (false, i.2) ∪ arc (true, i.1))
    (hpair : Pairwise (fun i j => disk i ∩ disk j ⊆ ⋃ k, arc k))
    (hwhole : (⋃ i, disk i) = F)
    (hlink : ∀ i : Bool, arc (true, i) = (F ∩ S) ∩ {x | weakSign i (A x)})
    (hheight : ∀ i : Bool, disk (i, false) ∪ disk (i, true) =
      F ∩ {x | weakSign i (A x)})
    (ψ : Bool → (ℝ × ℝ) → E) (r : Bool → ℝ) (j : Bool)
    (hpositive : ∀ k, ψ k '' ({0} ×ˢ uIcc 0 (r k)) ⊆ arc (false, j))
    (hnegative : ∀ k, ψ k '' ({0} ×ˢ uIcc 0 (-r k)) ⊆ arc (false, !j)) :
    ∃ arc' disk' : Bool × Bool → Set E,
      (∀ i, arc' (true, i) = arc (true, i)) ∧
      (∀ i, arc' (false, i) = arc (false, if i then !j else j)) ∧
      (∀ i, disk' i = disk (i.1, if i.2 then !j else j)) ∧
      (⋃ i, arc' i) = (⋃ i, arc i) ∧
      (∀ i, IsFinitePLBallPair ℝ (arc' i) {a, b}) ∧
      Pairwise (fun i l => arc' i ∩ arc' l = {a, b}) ∧
      (∀ i, IsFinitePLBallPair (ℝ × ℝ) (disk' i)
        (arc' (false, i.2) ∪ arc' (true, i.1))) ∧
      (∀ i, disk' i ∩ (⋃ k, arc' k) = arc' (false, i.2) ∪ arc' (true, i.1)) ∧
      Pairwise (fun i l => disk' i ∩ disk' l ⊆ ⋃ k, arc' k) ∧
      (⋃ i, disk' i) = F ∧
      (∀ i : Bool, arc' (true, i) = (F ∩ S) ∩ {x | weakSign i (A x)}) ∧
      (∀ i : Bool, disk' (i, false) ∪ disk' (i, true) =
        F ∩ {x | weakSign i (A x)}) ∧
      ∀ i k : Bool,
        ψ k '' ({0} ×ˢ uIcc 0 (if i then -r k else r k)) ⊆ arc' (false, i) := by
  let σ : Bool → Bool := fun i => if i then !j else j
  let τ : Bool × Bool → Bool × Bool := fun i =>
    (i.1, if i.1 then i.2 else σ i.2)
  let υ : Bool × Bool → Bool × Bool := fun i => (i.1, σ i.2)
  have hτ : Function.Involutive τ := by
    rintro ⟨i, k⟩
    cases j <;> cases i <;> cases k <;> rfl
  have hυ : Function.Involutive υ := by
    rintro ⟨i, k⟩
    cases j <;> cases i <;> cases k <;> rfl
  let arc' : Bool × Bool → Set E := arc ∘ τ
  let disk' : Bool × Bool → Set E := disk ∘ υ
  have hgraph : (⋃ i, arc' i) = (⋃ i, arc i) := hτ.surjective.iUnion_comp arc
  have hcover : (⋃ i, disk' i) = F := (hυ.surjective.iUnion_comp disk).trans hwhole
  refine ⟨arc', disk', fun _ => rfl, fun _ => rfl, fun _ => rfl,
    hgraph, fun i => hArc (τ i), ?_, fun i => hDisk (υ i), ?_, ?_, hcover,
    hlink, ?_, ?_⟩
  · intro i l hil
    exact hArcInter (fun h => hil (hτ.injective h))
  · intro i
    change disk (υ i) ∩ (⋃ k, arc' k) = _
    rw [hgraph]
    exact hcontact (υ i)
  · intro i l hil
    change disk (υ i) ∩ disk (υ l) ⊆ ⋃ k, arc' k
    rw [hgraph]
    exact hpair (fun h => hil (hυ.injective h))
  · intro i
    cases j
    · exact hheight i
    · exact (union_comm (disk (i, true)) (disk (i, false))).trans (hheight i)
  · intro i k
    cases i
    · exact hpositive k
    · exact hnegative k

end Geometry
