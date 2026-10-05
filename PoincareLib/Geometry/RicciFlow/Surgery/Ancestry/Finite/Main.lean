import PoincareLib.Geometry.RicciFlow.Surgery.Ancestry.Theory
import PoincareLib.Geometry.RicciFlow.Surgery.Ancestry.Finite.PoincareConstructor

/-!
# M56 finite ancestry and component paths proof entry

Natural-language theorem: for the actual changing-carrier surgery flow and
the reviewed M38/M54/M55 event adapters, with a connected nonempty initial
slice and a trivial initial fundamental group at every point,
assume an event witness with trivial parent groups at every M54-selected
survivor basepoint of every nonempty event, simply connected children, and
literal M38/M54/M55 provenance. Under these additional event hypotheses,
every terminal point lies on a coherent component path starting at one fixed
selected initial component.  Regular slabs use the actual flow transports;
surgery events retain an inherited point from the selected parent, and every
bounded interval contains only finitely many surgery times.  A finite family
of these paths covers each terminal slice.

Source: blueprint `def:path-of-components` (`52c756bceff7`) and
`thm:component-fundamental-group-persistence` (`5f0941d364d0`), source file
`extinction-and-component-topology.tex:8-29,549-579`; Morgan--Tian Definition
18.2 and the surgery continuation discussion
(`references/derived/MT2007.txt:20566-20596`), Proposition 15.3
(`references/derived/MT2007.txt:17814-17820`), and Proposition 15.12's
retained-region map (`references/derived/MT2007.txt:18174-18193`).  The
retained-region correction is recorded in
`reviews/errata/2026-09-10-surgery-extinction-audit.md:42-47,132-137`.

The helpers construct the stored-reference event gap, retained-interior
overlap, finite component traces, smooth path models and provider witness.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

/- Natural-language theorem, conditional branch: for the actual M52 flow,
assume a connected initial slice, trivial initial groups and an
event witness with trivial parent groups at every M54-selected survivor
basepoint, simply connected children and literal M38/M54/M55 provenance.
Produce component paths through every terminal point, all starting at one
fixed initial component, using actual slab maps and retained interior overlap,
with group persistence, finite terminal covers and bounded event counts.

Poincare branch: for a compact simply connected initial manifold, its
normalized metric, the actual M52 global flow and raw M38 topology on that
flow, construct the event witness and finite ancestry from M54/M55. Each
event uses the literal supplied M38 conclusion and selected M54/M55 outputs;
every selected component of every slice is simply connected. Neither an
all-event trivial-group premise nor extinction is assumed in this branch.

The construction owns finite chronological induction, retained interior
overlap, and the fixed initial component. Compact pre-flow smoothness and
curvature naturality contradict `maximal_intervals` at any surgery strictly
between an event's stored `tMinus` and its time; this justifies the actual
stored-reference/slab coherence. The raw cap and negative-neck fields give
retained overlap for each survivor.

Sources: Morgan--Tian Proposition 15.3, pp. 357--358; Corollary 15.4's finite
history, pp. 358--359; Definition 18.2 and following discussion, pp. 419--420.
See `reviews/contracts/2026-09-17-m56-poincare-producer-round1.md` and the
retained-region correction cited above. -/
/-- Finite anchored ancestry and the actual Poincare event witness of
Morgan--Tian Definition 18.2, pp. 419--420. -/
theorem repairedFiniteAncestry : RepairedAncestryTheory.{u} := by
  refine { ancestry := ?_, poincare := m56PoincareConstructor }
  intro _G38 G54 _G55 M _ _ _ _ _ _ _ _ _ N D _ F hF W hconn hgroups _ _ _
  exact m56FiniteAncestry G54 (hF ▸ W) hconn hgroups
    (fun H _ => D.certificate.local_finite (Set.Icc 0 H) isCompact_Icc)

end PoincareMT
