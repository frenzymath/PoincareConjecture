import PoincareLib.Geometry.RicciFlow.Extinction.Width.Class.IdentificationTheory
import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Families.IdentityComponent
import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Families.RegularHomotopy
import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Families.RegularPostcomposition
import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Families.RelativeFaithful
import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Families.RelativePostcomposition
import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Families.SphereQuotient
import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Families.CircleQuotient

/-!
# Assembly of the coherent M59 system

All proved clauses are assembled here. The two remaining inputs are the
natural pi2/pi3 comparison and free-class faithfulness. The latter must be
supplied by the cover argument using the applied M02 provider. This file
introduces no admission. Source: MT Claim 18.16 and Definition 18.17, p. 430.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Topology unitInterval

universe u

namespace PoincareMT

/-- The comparison and its actual-postcomposition law, separated from the
other already proved core fields. Source: MT Claim 18.16, p. 430. -/
structure M59ComparisonService where
  comparison : ∀ {M : Type u} [TopologicalSpace M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    [T2Space M] [SecondCountableTopology M]
    (_compact : IsCompact (Set.univ : Set M))
    (_connected : IsConnected (Set.univ : Set M))
    (x : M) (_piTwo : Subsingleton (HomotopyGroup.Pi 2 M x)),
      HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := M)) (constantC1Loop x) ≃*
        HomotopyGroup.Pi 3 M x
  naturality : ∀ {M N : Type u}
    [TopologicalSpace M] [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    [T2Space M] [SecondCountableTopology M]
    [TopologicalSpace N] [ChartedSpace LoopAmbient N] [IsManifold (𝓡 3) ∞ N]
    [T2Space N] [SecondCountableTopology N]
    (compactM : IsCompact (Set.univ : Set M)) (connectedM : IsConnected (Set.univ : Set M))
    (compactN : IsCompact (Set.univ : Set N)) (connectedN : IsConnected (Set.univ : Set N))
    (x : M) (y : N)
    (piTwoM : Subsingleton (HomotopyGroup.Pi 2 M x))
    (piTwoN : Subsingleton (HomotopyGroup.Pi 2 N y))
    (f : C(M, N)) (_smooth : ContMDiff (𝓡 3) (𝓡 3) ∞ f) (based : f x = y)
    (L : M59LoopPostcomposition f)
    (alpha : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := M)) (constantC1Loop x)),
      comparison compactN connectedN y piTwoN
        (surgeryHomotopyMap (n := 2) L.map (L.map_based based) alpha) =
      surgeryHomotopyMap (n := 3) f based (comparison compactM connectedM x piTwoM alpha)

/-- The precise remaining free-class implication. Its proof requires the
compact and noncompact cover arguments, including applied M02 in the compact
case. Source: Hatcher 4A.2 and 2C.3; MT Claim 18.16, p. 430. -/
def M59FreeClassFaithfulness (q : M59SphereQuotient) : Prop :=
  ∀ {M : Type u} [TopologicalSpace M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    [T2Space M] [SecondCountableTopology M]
    (_compact : IsCompact (Set.univ : Set M))
    (_connected : IsConnected (Set.univ : Set M))
    (x : M) (_piTwo : Subsingleton (HomotopyGroup.Pi 2 M x))
    (Gamma Delta : FreeTwoSphereFamily (M := M)),
      M59NormalizedAt q x Gamma → M59NormalizedAt q x Delta →
      (m59FamilyMap Gamma).Homotopic (m59FamilyMap Delta) →
        familySigmaClass Gamma = familySigmaClass Delta

/-- Assemble every core field from the comparison and free-class implication.
Source: MT Claim 18.16 and Definition 18.17, p. 430. -/
noncomputable def m59IdentificationCore_of_comparison_and_free_class
    (q : M59SphereQuotient) (C : M59ComparisonService.{u}) (hfree : M59FreeClassFaithfulness.{u} q)
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    [T2Space M] [SecondCountableTopology M]
    (hcompact : IsCompact (Set.univ : Set M)) (hconnected : IsConnected (Set.univ : Set M))
    (x : M) (hpi : Subsingleton (HomotopyGroup.Pi 2 M x)) : M59IdentificationCore q x where
  pi_two_pi_three := C.comparison hcompact hconnected x hpi
  identity_component := m59_identity_component hcompact hconnected x
  regular_representatives := m59_regular_representatives q x
  raw_regularization := m59_raw_regularization hcompact hconnected q x
  free_class_identification Gamma Delta hGamma hDelta :=
    ⟨hfree hcompact hconnected x hpi Gamma Delta hGamma hDelta,
      fun h => ⟨(m59SphereHomotopy_of_class_eq q x Gamma Delta hGamma hDelta h).choose⟩⟩
  regular_homotopy Gamma Delta hGamma hDelta h :=
    m59_regular_homotopy_of_class_eq q x Gamma Delta hGamma hDelta
      (hfree hcompact hconnected x hpi Gamma Delta hGamma hDelta h)
  relative_surjective := m59_relative_surjective m59CircleQuotient.pole x
  relative_faithful := m59_relative_faithful m59CircleQuotient.pole x hpi

/-- The full frozen system follows from exactly the two outstanding services.
All other fields use their proved implementations. Source: MT Claim 18.16
and Definition 18.17, p. 430. -/
noncomputable def m59IdentificationSystem_of_comparison_and_free_class
    (C : M59ComparisonService.{u}) (hfree : M59FreeClassFaithfulness.{u} m59SphereQuotient) :
    M59IdentificationSystem.{u} where
  quotient := m59SphereQuotient
  core := m59IdentificationCore_of_comparison_and_free_class m59SphereQuotient C hfree
  postcomposition f hf := ⟨m59LoopPostcomposition f hf⟩
  regular_postcomposition := m59_regular_postcomposition
  naturality := C.naturality
  relative_naturality := m59_relative_naturality

end PoincareMT
