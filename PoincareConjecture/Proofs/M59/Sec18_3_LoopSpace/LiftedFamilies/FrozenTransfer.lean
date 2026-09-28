import PoincareConjecture.Proofs.M59.Sec18_3_LoopSpace.LiftedFamilies.Transfer
import PoincareConjecture.Proofs.M59.Sec18_3_LoopSpace.NormalizedFreeHomotopy











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology unitInterval

namespace PoincareConjecture

open Proofs.M02 Proofs.M59

variable {M E : Type*} [TopologicalSpace M] [TopologicalSpace E]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M] [T2Space M]
  [SimplyConnectedSpace E]





theorem m59_normalized_classes_eq_of_cover_deck
    (hcompact : IsCompact (univ : Set M)) (q : M59SphereQuotient)
    (p : E → M) (hp : IsCoveringMap p) (c : E)
    (hpi : Subsingleton (HomotopyGroup.Pi 2 E c))
    (hdeck : ∀ (c' : E), p c' = p c → ∀ r : Path c c',
      ∃ (d : C(E, E)) (hd : d c = c'),
        (∀ e, p (d e) = p e) ∧
          ∀ A : HomotopyGroup.Pi 3 E c,
            homotopyGroupMap (Fin 3) d hd A =
              (m59HigherBasepointTransport E 3).map r A)
    (Gamma Delta : FreeTwoSphereFamily (M := M))
    (hGamma : M59NormalizedAt q (p c) Gamma) (hDelta : M59NormalizedAt q (p c) Delta)
    (hfree : (m59FamilyMap Gamma).Homotopic (m59FamilyMap Delta)) :
    familySigmaClass Gamma = familySigmaClass Delta := by
  exact m59_normalized_classes_eq_of_continuous_free_class hcompact q (p c)
    (fun _ _ _ H => hp.homotopic_circle_families_of_deck_piThree
      m59CircleQuotient c hpi hdeck H) Gamma Delta hGamma hDelta hfree

end PoincareConjecture
