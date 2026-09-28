import PoincareConjecture.Proofs.M59.Mathlib.PathClassUniversal
import PoincareConjecture.Proofs.M59.Mathlib.CoveringHomotopyGroups
import PoincareConjecture.Proofs.M59.Mathlib.CoveringManifold
import PoincareConjecture.Proofs.M59.Sec18_3_LoopSpace.NoncompactCover
import PoincareConjecture.Proofs.M59.Sec18_3_LoopSpace.Claim18_16_PiTwoPiThree











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology unitInterval

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M] [ChartedSpace LoopAmbient M] [T2Space M]



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

end PoincareConjecture
