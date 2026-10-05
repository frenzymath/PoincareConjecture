import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Comparison.PathClassUniversal
import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Comparison.CoveringHomotopyGroups
import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Comparison.CoveringManifold
import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Families.NoncompactCover
import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Families.Claim18_16_PiTwoPiThree

/-!
# Free-class faithfulness when the universal cover is noncompact

Apply top-dimensional homology vanishing to the actual path-class cover,
transfer pi2 and pi3 through its covering map, and use the proved loop
comparison. In this case all normalized based family classes coincide.
Source: MT Claim 18.16, printed p. 430; Hatcher, Propositions 3.29 and 4.1,
printed pp. 239 and 342.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology unitInterval

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M] [ChartedSpace LoopAmbient M] [T2Space M]

/-- A connected three-manifold with trivial pi2 and noncompact path-class
cover has trivial pi3. Source: MT Claim 18.16, p. 430; Hatcher 3.29 and 4.1. -/
theorem m59_piThree_subsingleton_of_noncompact_pathCover
    (hconnected : IsConnected (univ : Set M)) (x : M)
    (hpi : Subsingleton (HomotopyGroup.Pi 2 M x))
    (hnoncompact : ¬IsCompact (univ : Set (PathClassCover x))) :
    Subsingleton (HomotopyGroup.Pi 3 M x) := by
  let : ConnectedSpace M := connectedSpace_iff_univ.mpr hconnected
  let : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace LoopAmbient M
  let : PathConnectedSpace M := PathConnectedSpace.of_locallyPathConnectedSpace
  let : LocallySimplyConnectedSpace M := ChartedSpace.locallySimplyConnectedSpace LoopAmbient M
  let hp := PathClassCover.isCoveringMap_endpoint x
  let : T2Space (PathClassCover x) := hp.t2Space
  let : ChartedSpace LoopAmbient (PathClassCover x) := hp.isLocalHomeomorph.pullbackChartedSpace
  let : Subsingleton (HomotopyGroup.Pi 2 M x) := hpi
  have hpiCover : Subsingleton (HomotopyGroup.Pi 2 (PathClassCover x)
      (PathClassCover.basepoint x)) := by
    constructor
    intro a b
    exact (hp.homotopyGroupEquiv (N := Fin 2) (PathClassCover.basepoint x)).injective
      (hpi.elim _ _)
  let : Subsingleton (HomotopyGroup.Pi 3 (PathClassCover x) (PathClassCover.basepoint x)) :=
    Proofs.M59.noncompactSimplyConnectedThree_piThree_subsingleton
      (PathClassCover.basepoint x) hnoncompact hpiCover
  exact (hp.homotopyGroupEquiv (N := Fin 3) (PathClassCover.basepoint x)).surjective.subsingleton

/-- The noncompact-cover branch proves equality of all normalized family
classes, hence in particular free-class faithfulness.
Source: MT Claim 18.16, printed p. 430. -/
theorem m59_normalized_classes_eq_of_noncompact_pathCover [IsManifold (𝓡 3) ∞ M]
    (hcompact : IsCompact (univ : Set M)) (hconnected : IsConnected (univ : Set M))
    (q : M59SphereQuotient) (x : M) (hpi : Subsingleton (HomotopyGroup.Pi 2 M x))
    (hnoncompact : ¬IsCompact (univ : Set (PathClassCover x)))
    (Gamma Delta : FreeTwoSphereFamily (M := M))
    (hGamma : M59NormalizedAt q x Gamma) (hDelta : M59NormalizedAt q x Delta) :
    familySigmaClass Gamma = familySigmaClass Delta := by
  let : Subsingleton (HomotopyGroup.Pi 3 M x) :=
    m59_piThree_subsingleton_of_noncompact_pathCover hconnected x hpi hnoncompact
  let : Subsingleton (HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := M)) (constantC1Loop x)) :=
    (m59PiTwoPiThree hcompact x hpi).injective.subsingleton
  rw [← m59NormalizedCube_sigma q x Gamma hGamma, ← m59NormalizedCube_sigma q x Delta hDelta]
  exact congrArg (Sigma.mk x) (Subsingleton.elim _ _)

end PoincareMT
