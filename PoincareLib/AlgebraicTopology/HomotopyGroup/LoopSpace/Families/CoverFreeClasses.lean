import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Families.NoncompactFreeClasses
import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Families.LiftedFamilies.FrozenTransfer

/-!
# Free-class faithfulness from the two covering-space cases

Use the actual path-class cover. A noncompact cover has vanishing pi3 by
the proved support and Hurewicz argument. For a compact cover, pull back
the smooth atlas and use the deck-action conclusion to transfer lifted
family homotopies. The one retained input here is the compact finite-model
calculation, which must be proved using the applied M02 provider.
Source: MT Claim 18.16, printed p. 430; Hatcher, Theorems 2C.3 and 4.32.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology unitInterval

universe u

namespace PoincareMT

/-- The remaining compact-cover calculation, stated for actual deck maps
and the fixed cubical transport. Its proof applies the supplied M02 to
the covering manifold before computing the finite-model trace.
Source: Hatcher, Theorem 2C.3; MT Claim 18.16, printed p. 430. -/
def M59CompactCoverDeckAction : Prop :=
  ∀ {M E : Type u}
    [TopologicalSpace M] [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M] [ConnectedSpace M]
    [TopologicalSpace E] [ChartedSpace LoopAmbient E] [IsManifold (𝓡 3) ∞ E]
    [T2Space E] [SecondCountableTopology E] [CompactSpace E] [SimplyConnectedSpace E]
    (p : C(E, M)), IsCoveringMap p → ∀ (d : C(E, E)), p.comp d = p →
      ∀ (c : E) (r : Path c (d c)) (a : HomotopyGroup.Pi 3 E c),
        surgeryHomotopyMap (n := 3) d rfl a =
          (m59HigherBasepointTransport E 3).map r a

/-- The two cover cases prove exactly the frozen free-class implication.
All covering existence, lifting, regularity and transport work is discharged;
only the compact deck calculation is retained as a premise.
Source: MT Claim 18.16, printed p. 430; Hatcher 3.29, 4.1 and 4A.2. -/
theorem m59FreeClassFaithfulness_of_compact_cover_deck
    (hdeck : M59CompactCoverDeckAction.{u}) (q : M59SphereQuotient) :
    M59FreeClassFaithfulness.{u} q := by
  classical
  intro M _ _ _ _ _ hcompact hconnected x hpi Gamma Delta hGamma hDelta hfree
  let : CompactSpace M := isCompact_univ_iff.mp hcompact
  let : ConnectedSpace M := connectedSpace_iff_univ.mpr hconnected
  let : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace LoopAmbient M
  let : PathConnectedSpace M := PathConnectedSpace.of_locallyPathConnectedSpace
  let : LocallySimplyConnectedSpace M := ChartedSpace.locallySimplyConnectedSpace LoopAmbient M
  by_cases hcover : IsCompact (univ : Set (PathClassCover x))
  · let hp := PathClassCover.isCoveringMap_endpoint x
    let : CompactSpace (PathClassCover x) := isCompact_univ_iff.mp hcover
    let : T2Space (PathClassCover x) := hp.t2Space
    let : ChartedSpace LoopAmbient (PathClassCover x) := hp.isLocalHomeomorph.pullbackChartedSpace
    let : IsManifold (𝓡 3) ∞ (PathClassCover x) :=
      hp.isLocalHomeomorph.pullback_isManifold (𝓡 3) ∞
    let : SecondCountableTopology (PathClassCover x) :=
      ChartedSpace.secondCountable_of_sigmaCompact LoopAmbient (PathClassCover x)
    let c := PathClassCover.basepoint x
    let p : C(PathClassCover x, M) := ⟨PathClassCover.endpoint, hp.continuous⟩
    have hpiCover : Subsingleton (HomotopyGroup.Pi 2 (PathClassCover x) c) := by
      constructor
      intro a b
      exact (hp.homotopyGroupEquiv (N := Fin 2) c).injective (hpi.elim _ _)
    apply m59_normalized_classes_eq_of_cover_deck hcompact q p hp c hpiCover
      ?_ Gamma Delta hGamma hDelta hfree
    intro c' hc' r
    obtain ⟨alpha, halpha⟩ := PathClassCover.exists_deck_apply_eq c c' hc'.symm
    let d : C(PathClassCover x, PathClassCover x) :=
      ⟨PathClassCover.deck alpha, (PathClassCover.deck alpha).continuous⟩
    have hd : d c = c' := halpha
    refine ⟨d, hd, fun _ => rfl, ?_⟩
    subst c'
    intro a
    exact hdeck p hp d (by ext e; rfl) c r a
  · exact m59_normalized_classes_eq_of_noncompact_pathCover
      hcompact hconnected q x hpi hcover Gamma Delta hGamma hDelta

/-- The complete identification system follows from the single compact
deck calculation. Source: MT Claim 18.16, printed p. 430. -/
noncomputable def m59IdentificationSystem_of_compact_cover_deck
    (hdeck : M59CompactCoverDeckAction.{u}) : M59IdentificationSystem.{u} :=
  m59IdentificationSystem_of_free_class
    (m59FreeClassFaithfulness_of_compact_cover_deck hdeck m59SphereQuotient)

end PoincareMT
