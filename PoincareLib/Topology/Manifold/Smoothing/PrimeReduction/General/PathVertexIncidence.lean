import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.FiniteSegmentCorrespondence
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Graphs.PolygonPathCycles
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.RadialRescaling

/-!
# Original vertex incidence in a returning path

The literal path segments generate a geometric complex. Its vertex
incidence theorem excludes an endpoint lying inside a remote edge.
See Kneser1929 p.254 and Prime020, vertex incidence.
-/

set_option autoImplicit false

open Set Geometry

namespace Polygon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

/-- Every original vertex lying on a faithful path edge is one of
that edge's two endpoints. Injectivity alone would not suffice;
the entire segment intersection law constructs the same complex.
See Prime020, vertex incidence. -/
theorem path_vertex_mem_segment_iff (p : Fin (n + 2) → E)
    (hp : Function.Injective p)
    (hinter : ∀ i j : Fin (n + 1),
      segment ℝ (p i.castSucc) (p i.succ) ∩ segment ℝ (p j.castSucc) (p j.succ) ⊆
        convexHull ℝ (({p i.castSucc, p i.succ} : Set E) ∩ {p j.castSucc, p j.succ}))
    (k : Fin (n + 2)) (i : Fin (n + 1)) :
    p k ∈ segment ℝ (p i.castSucc) (p i.succ) ↔
      p k = p i.castSucc ∨ p k = p i.succ := by
  classical
  have hne (j : Fin (n + 1)) : p j.castSucc ≠ p j.succ := by
    intro h
    have hv := congrArg Fin.val (hp h)
    change j.val = j.val + 1 at hv
    omega
  obtain ⟨K, _, hfaces, _⟩ := SimplicialComplex.exists_finite_segment_complex
    (fun j : Fin (n + 1) => p j.castSucc) (fun j => p j.succ) hne hinter
  have hedge (j : Fin (n + 1)) : ({p j.castSucc, p j.succ} : Finset E) ∈ K.faces :=
    (hfaces _).mpr ⟨Finset.insert_nonempty _ _, j, Finset.Subset.refl _⟩
  have hv (j : Fin (n + 2)) : p j ∈ K.vertices := by
    induction j using Fin.lastCases with
    | last =>
      exact K.face_subset_vertices (hedge (Fin.last n))
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    | cast j => exact K.face_subset_vertices (hedge j) (Finset.mem_insert_self _ _)
  simpa only [Finset.coe_pair, convexHull_pair, Finset.mem_insert, Finset.mem_singleton]
    using K.vertex_mem_convexHull_iff (hv k) (hedge i)

end Polygon
