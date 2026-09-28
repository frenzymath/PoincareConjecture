import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.Critical
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.Boundary
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.Interior
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.CriticalSet.Extrema

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.SphereMorseReduction

private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

variable {f : S2 -> E3} (M : SphereMorseReduction f)

theorem core_ne_univ {g : S2 -> E3} (hg : g ∈ M.tree.leaves)
    (P : SphereSurgeryPath (M.v : E3) (fun p => M.D (f p)) g) : P.core ≠ univ := by
  let : Nontrivial S2 := ⟨⟨M.v, -M.v, ne_neg_of_mem_unit_sphere Real M.v⟩⟩
  intro hcore
  obtain ⟨p, q, hpq, hp, hq⟩ := Poincare.Geometry.Manifold.exists_two_distinct_critical_points
    ((innerSL Real (M.v : E3)).contMDiff.comp (M.tree.embedding_of_mem_leaves hg).contMDiff)
  exact hpq (M.subsingleton_critical_core hg P
    ⟨by rw [hcore]; trivial, hp⟩ ⟨by rw [hcore]; trivial, hq⟩)

theorem model_cap_list_ne_nil {g : S2 -> E3} (hg : g ∈ M.tree.leaves)
    (P : SphereSurgeryPath (M.v : E3) (fun p => M.D (f p)) g)
    {B : Set Real} (L : List (SphereSurgeryCoreCap (M.v : E3) g B))
    (hcore : P.core = (⋃ D ∈ L, D.chart '' ball 0 1)ᶜ) : L ≠ [] := by
  intro hL
  apply M.core_ne_univ hg P
  simpa only [hL, List.not_mem_nil, iUnion_of_empty, iUnion_empty, compl_empty] using hcore

end Poincare.Manifold.Schoenflies.SphereMorseReduction

namespace Poincare.Manifold.Schoenflies.SphereSurgeryPath

private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

theorem exists_cap_height_bounds_of_regular
    {v : E3} {f g : S2 -> E3} (P : SphereSurgeryPath v f g)
    (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g)
    (hcap : P.PreservesCaps) {B : Set Real}
    (L : List (SphereSurgeryCoreCap v g B))
    (hpair : L.Pairwise (fun D E => Disjoint
      (D.chart '' closedBall 0 1) (E.chart '' closedBall 0 1)))
    (hcore : P.core = (⋃ D ∈ L, D.chart '' ball 0 1)ᶜ)
    (hreg : ∀ p ∈ P.core, mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun q => inner Real v (g q)) p ≠ 0) :
    ∃ D ∈ L, ∃ E ∈ L,
      (∃ p ∈ P.core, inner Real v (g p) = D.center) ∧
      (∃ q ∈ P.core, inner Real v (g q) = E.center) ∧
      (∀ p ∈ P.core, D.center ≤ inner Real v (g p) ∧
        inner Real v (g p) ≤ E.center) ∧
      D.center < E.center ∧ D ≠ E ∧
      ∀ p ∈ interior P.core, D.center < inner Real v (g p) ∧
        inner Real v (g p) < E.center := by
  obtain ⟨p, hp, q, hq, hmin, hmax⟩ :=
    Poincare.Geometry.Manifold.exists_boundary_extrema_of_regular
      ((innerSL Real v).contMDiff.comp hg.contMDiff) P.isClosed_core.isCompact
      (P.isConnected_core hcap).nonempty hreg
  have hpK := P.isClosed_core.frontier_subset hp
  have hqK := P.isClosed_core.frontier_subset hq
  rw [SphereSurgeryCoreCap.frontier_core L hpair hcore] at hp hq
  simp only [mem_iUnion] at hp hq
  obtain ⟨D, hD, hpD⟩ := hp
  obtain ⟨E, hE, hqE⟩ := hq
  have hpheight := D.height_eq_on_boundary p hpD
  have hqheight := E.height_eq_on_boundary q hqE
  have hstrict := Poincare.Geometry.Manifold.strict_bounds_on_interior_of_regular
    ((innerSL Real v).contMDiff.comp hg.contMDiff) hmin hmax hreg
  obtain ⟨x, hx⟩ := SphereSurgeryCoreCap.interior_core_nonempty L hpair hcore
  have hlt : D.center < E.center := by
    rw [← hpheight, ← hqheight]
    exact (hstrict x hx).1.trans (hstrict x hx).2
  refine ⟨D, hD, E, hE, ⟨p, hpK, hpheight⟩, ⟨q, hqK, hqheight⟩,
    fun x hx => ⟨hpheight ▸ hmin hx, hqheight ▸ hmax hx⟩,
    hlt, fun heq => hlt.ne (congrArg SphereSurgeryCoreCap.center heq), ?_⟩
  intro y hy
  exact ⟨hpheight ▸ (hstrict y hy).1, hqheight ▸ (hstrict y hy).2⟩

end Poincare.Manifold.Schoenflies.SphereSurgeryPath
