import PoincareLib.Geometry.RicciFlow.Surgery.Ancestry.Children
import PoincareLib.Topology.Manifold.Surgery.GroupEffects.Statement

/-!
# M55 repaired surviving-child component statement

The factor and injection effects of M54 imply simple connectedness of every
surviving child component.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/-
Natural-language theorem: for a realized finite connected-sum surgery
conclusion, assume the parent fundamental group at each survivor basepoint is
trivial and use the exact M54 factor/injection certificate.  Then each
survivor piece has trivial fundamental group and is simply connected; its
survivor region is identified with a connected component of the post-surgery
carrier by an explicit point/specification witness.

Source: Morgan--Tian Proposition 15.3 (printed pp. 357-358; source text
`references/derived/MT2007.txt:17814-17820`) and the connected-sum
fundamental-group calculation in blueprint
`thm:connected-sum-fundamental-group` (`topological-endgame.tex:1260-1284`).
The aggregate persistence node is
`MT.18.topology.fundamental_group_persistence`; Claims 18.19-18.20 (printed
p. 431) are downstream motivation, not direct premises here. The correction
record is `reviews/errata/2026-09-10-surgery-extinction-audit.md:42-47,132-137`.
-/
structure RepairedChildComponentsTheory : Prop where
  components : ∀ (G54 : RepairedGroupEffectsTheory.{u}),
    ∀ {A B : GeneralizedSliceCarrier.{u}}
      (C : SurgeryTopologyConclusion A B)
      (E : RepairedSurgeryGroupEffectsData C)
      (_hE : E = Classical.choice (G54.effects C)),
      (parent_groups_subsingleton :
        ∀ (i : Fin C.piece_count) (hi : C.kind i = .survivor),
          ∀ x : (C.piece i).carrier,
            Subsingleton (FundamentalGroup A.carrier
              (E.parent_basepoint i hi x))) →
      Nonempty (RepairedChildComponentsData C E)

end PoincareMT
