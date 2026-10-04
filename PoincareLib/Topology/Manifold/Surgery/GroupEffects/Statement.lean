import PoincareLib.Geometry.RicciFlow.Surgery.Ancestry.GroupEffects

/-! Adapted from Mapher `PoincareMT/Statements/M54GroupEffects.lean` at
`0c5d5c4e1ecbc12703b1994e226df1b15d2e8d39`; see `references/ricci-flow/mapher/group-effects.md`. -/

/-!
# M54 repaired surgery fundamental-group effects statement
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/-
Natural-language theorem (local group bridge and persistence interface): Given
a finite connected-sum surgery conclusion, every surviving summand has the
factor homomorphism, kernel, and injective section supplied by van Kampen.
For a bounded component path with finitely many surgery times, if the initial
component group is trivial, it remains trivial at every selected time slice.

Source: blueprint `thm:component-fundamental-group-persistence`
(`5f0941d364d0`), `def:path-of-components` (`52c756bceff7`), and
`thm:connected-sum-fundamental-group` (`0783c5d92731`),
`extinction-and-component-topology.tex:548-579`; Morgan--Tian Proposition
15.3 (printed pp. 357-358), the path and group-theory discussion around
Definition 18.2 and Lemma 18.3 (pp. 421-422), specialized to trivial initial
groups. At surgery the supplied injection into the trivial parent suffices;
no general Kurosh/free-factor closure theorem is asserted here.
Claims 18.19-18.20 (p. 431) are downstream
motivation, not direct proof premises. The surgery erratum is recorded in
`reviews/errata/2026-09-10-surgery-extinction-audit.md:42-47,132-137`.
The connected-sum group calculation is blueprint
`topological-endgame.tex:1260-1284`; the finite-interval surgery bound is
`kappa-solutions-and-surgery-continuation.tex:1549-1555`.

The `effects` field is an explicit local adapter consumed by M55; its proof
obtains the maps from `C.reconstruction`, and later event witnesses instantiate
that certificate.  The `persistence` field exposes the bounded-flow theorem as
primitive algebraic path data, so its proof does not hide the finite induction
behind a packaged theorem hypothesis.  The spacetime path and retention
coherence are supplied by M56.
-/
structure RepairedGroupEffectsTheory : Prop where
  effects : ∀ {A B : GeneralizedSliceCarrier.{u}}
      (C : SurgeryTopologyConclusion A B),
      Nonempty (RepairedSurgeryGroupEffectsData.{u} C)
  persistence : ∀ (F : SurgeryFlowData.{u}) (T : ℝ)
      (component : ∀ s : Set.Icc (0 : ℝ) T,
        SurgerySelectedComponent (F.slice s.1))
      (I : RepairedGroupPersistenceInput F T component),
      Nonempty (RepairedGroupPersistenceData F T component I)

end PoincareMT
