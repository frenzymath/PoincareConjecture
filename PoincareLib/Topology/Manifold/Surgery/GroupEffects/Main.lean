import PoincareLib.Topology.Manifold.Surgery.GroupEffects.Statement
import PoincareLib.Topology.Manifold.Surgery.GroupEffects.Persistence
import PoincareLib.Topology.Manifold.Surgery.GroupEffects.ConnectedSum.Reconstruction

/-! Adapted from Mapher `PoincareMT/Proofs/M54.lean` at
`0c5d5c4e1ecbc12703b1994e226df1b15d2e8d39`; see `references/ricci-flow/mapher/group-effects.md`. -/

/-!
# M54 fundamental-group effects proof entry

Natural-language theorem: a finite connected-sum surgery conclusion supplies
the van Kampen factor and survivor injection for each surviving summand.  Along
a bounded component path with finitely many surgery times, a trivial initial
group remains trivial at every selected time. Use regular group equivalences
between events and the survivor injection into the trivial parent at events.

Source: blueprint node `thm:component-fundamental-group-persistence`
(`MT.18.topology.fundamental_group_persistence`), with the local factor
adapter split across `thm:connected-sum-fundamental-group` and
`thm:morgan-tian-proposition-15-3`.  The mathematical source is Morgan--Tian
Proposition 15.3 (printed pp. 357-358), the path and group-theory discussion
around Definition 18.2 and Lemma 18.3 (pp. 421-422), in the Poincare-specific
trivial-group case. Claims 18.19 and 18.20 (p. 431) are
downstream motivation rather than direct proof premises. Source text locations are
`references/derived/MT2007.txt:17814-17820`,
`references/derived/MT2007.txt:20566-20571`,
`references/derived/MT2007.txt:20643-20650`, and
`references/derived/MT2007.txt:21124-21139`.  The corrected surgery reading
is recorded in `reviews/errata/2026-09-10-surgery-extinction-audit.md:42-47,132-137`.

The local effect follows by van Kampen on the actual ball and collar
coordinates, followed by composition through the finite reconstruction.
Persistence uses induction on the number of surgery events up to each time.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

/-- The factor and injection effects of Proposition 15.3 (pp. 357-358), with
trivial-group persistence along the finite component path of Definition 18.2 (p. 419). -/
theorem repairedGroupEffects : RepairedGroupEffectsTheory.{u} := by
  exact ⟨repairedSurgeryGroupEffects, repairedGroupPersistence⟩

end PoincareMT
