import PoincareLib.Topology.Manifold.Smoothing.Dehn.General.Mathlib.AcyclicEdgeChains
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Polygons.Mathlib.TriangleChainKernel

/-!
# Connectedness of the actual complementary triangle graph

Only original shared edges outside the selected primal forest remain.
A component's actual triangle chain has boundary supported on that
forest. The bridge-cut proof kills the boundary, and full original
triangle adjacency makes the component label constant. See Dehn019
and Putman, The Classification of Surfaces, Theorem 5.1, pp. 15--16.
-/

set_option autoImplicit false

namespace PreAbstractSimplicialComplex.ModTwoCochains

variable {ι : Type*} (A : PreAbstractSimplicialComplex ι)

/-- Keep the actual shared edges outside the given primal graph.
The vertices are the unchanged original triangles. See Dehn019. -/
def complementaryTriangleGraph (T : SimpleGraph ι) : SimpleGraph (Triangle A) where
  Adj q r := q ≠ r ∧ ∃ e : Edge A,
    ¬edgeInGraph A T e ∧ e.val ⊆ q.val ∧ e.val ⊆ r.val
  symm := ⟨by
    rintro q r ⟨hqr, e, he, heq, her⟩
    exact ⟨Ne.symm hqr, e, he, her, heq⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

variable [Fintype ι]

/-- Deleting the primal forest leaves the actual triangle graph
connected. The proof constructs and evaluates the original component
chain, with every original coface retained. See Dehn derivation 019. -/
theorem complementaryTriangleGraph_connected (T : SimpleGraph ι) (hT : T.IsAcyclic)
    (hcofaces : ∀ e : Edge A, (triangleCofaces A e).card = 2)
    (htri : (triangleGraph A).Connected) :
    (complementaryTriangleGraph A T).Connected := by
  classical
  let G := complementaryTriangleGraph A T
  let : Nonempty (Triangle A) := htri.nonempty
  refine ⟨?_⟩
  intro q r
  by_contra hnot
  let a : Triangle A → ZMod 2 := fun t => if G.Reachable q t then 1 else 0
  let c := coordinateChainEquiv (Triangle A) a
  have hcoordinate (t : Triangle A) : c (Pi.single t 1) = a t := by
    convert coordinateChainEquiv_single (Triangle A) a t using 1
    congr 1
    funext s
    by_cases hs : s = t <;> simp [hs]
  have hcycle : (vertexCoboundary A).dualMap ((edgeCoboundary A).dualMap c) = 0 := by
    apply LinearMap.ext
    intro v
    change c (edgeCoboundary A (vertexCoboundary A v)) = 0
    rw [edgeCoboundary_vertexCoboundary, map_zero]
  have hsupport (e : Edge A) (he : ¬edgeInGraph A T e) :
      (edgeCoboundary A).dualMap c (Pi.single e 1) = 0 := by
    obtain ⟨s, t, hst, hpair⟩ := Finset.card_eq_two.mp (hcofaces e)
    have hes : e.val ⊆ s.val := (Finset.mem_filter.mp
      (show s ∈ triangleCofaces A e by rw [hpair]; simp)).2
    have het : e.val ⊆ t.val := (Finset.mem_filter.mp
      (show t ∈ triangleCofaces A e by rw [hpair]; simp)).2
    have hadj : G.Adj s t := ⟨hst, e, he, hes, het⟩
    have hast : a s = a t := by
      have h : G.Reachable q s ↔ G.Reachable q t :=
        ⟨fun hs => hs.trans hadj.reachable, fun ht => ht.trans hadj.symm.reachable⟩
      dsimp only [a]
      by_cases hs : G.Reachable q s
      · rw [if_pos hs, if_pos (h.mp hs)]
      · rw [if_neg hs, if_neg (fun ht => hs (h.mpr ht))]
    rw [boundary2_single_eq_sum_coordinates, hpair, Finset.sum_pair hst,
      hcoordinate, hcoordinate, hast]
    exact CharTwo.add_self_eq_zero (a t)
  have hc := edgeChain_eq_zero_of_acyclic_support A T hT
    ((edgeCoboundary A).dualMap c) hcycle hsupport
  have hconstant := boundary2_ker_coordinates_eq A (fun e => (hcofaces e).le)
    htri.preconnected c hc q r
  rw [hcoordinate, hcoordinate] at hconstant
  change (if G.Reachable q q then (1 : ZMod 2) else 0) =
    (if G.Reachable q r then (1 : ZMod 2) else 0) at hconstant
  rw [if_pos (SimpleGraph.Reachable.refl q), if_neg hnot] at hconstant
  exact one_ne_zero hconstant

end PreAbstractSimplicialComplex.ModTwoCochains
