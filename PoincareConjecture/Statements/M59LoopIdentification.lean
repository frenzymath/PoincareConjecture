import PoincareConjecture.Definitions.M59LoopIdentification
import PoincareConjecture.Definitions.Ch15.SurgeryComparison

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology ENNReal unitInterval

universe u

namespace PoincareConjecture

section Carrier

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

structure M59IdentificationCore (q : M59SphereQuotient) (x : M) where
  pi_two_pi_three :
    HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := M)) (constantC1Loop x) ≃*
      HomotopyGroup.Pi 3 M x
  identity_component : ∀ gamma : C1FreeLoopSpace (M := M),
    InIdentityComponent x gamma ↔ IsNullHomotopicLoop gamma
  regular_representatives :
    ∀ alpha : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := M)) (constantC1Loop x),
      ∃ Gamma : FreeTwoSphereFamily (M := M),
        M59NormalizedAt q x Gamma ∧ familySigmaClass Gamma = ⟨x, alpha⟩
  raw_regularization :
    ∀ F : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M)),
      (∀ c, IsNullHomotopicLoop (F c)) →
        ∃ Gamma : FreeTwoSphereFamily (M := M),
          M59NormalizedAt q x Gamma ∧ F.Homotopic (m59FamilyMap Gamma)
  free_class_identification :
    ∀ Gamma Delta : FreeTwoSphereFamily (M := M),
      M59NormalizedAt q x Gamma → M59NormalizedAt q x Delta →
        ((m59FamilyMap Gamma).Homotopic (m59FamilyMap Delta) ↔
          familySigmaClass Gamma = familySigmaClass Delta)

  regular_homotopy :
    ∀ Gamma Delta : FreeTwoSphereFamily (M := M),
      M59NormalizedAt q x Gamma → M59NormalizedAt q x Delta →
        (m59FamilyMap Gamma).Homotopic (m59FamilyMap Delta) →
          FreeTwoSphereHomotopic Gamma Delta
  relative_surjective :
    ∀ F : ContinuousMap (Fin 2 → I) (C1FreeLoopSpace (M := M)),
      M59RelativeLoopCubeAt x F →
        ∃ gamma : GenLoop (Fin 2) (C1FreeLoopSpace (M := M)) (constantC1Loop x),
          ContinuousMap.HomotopicWith F gamma.1 (M59RelativeLoopCubeAt x)
  relative_faithful :
    ∀ gamma delta : GenLoop (Fin 2) (C1FreeLoopSpace (M := M)) (constantC1Loop x),
      ContinuousMap.HomotopicWith gamma.1 delta.1 (M59RelativeLoopCubeAt x) ↔
        GenLoop.Homotopic gamma delta

end Carrier

structure M59IdentificationSystem where
  quotient : M59SphereQuotient
  core : ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
      [T2Space M] [SecondCountableTopology M]
      (_compact : IsCompact (Set.univ : Set M))
      (_connected : IsConnected (Set.univ : Set M))
      (x : M) (_pi_two_trivial : Subsingleton (HomotopyGroup.Pi 2 M x)),
      M59IdentificationCore quotient x
  postcomposition : ∀ {M N : Type u}
      [TopologicalSpace M] [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
      [TopologicalSpace N] [ChartedSpace LoopAmbient N] [IsManifold (𝓡 3) ∞ N]
      (f : ContinuousMap M N), ContMDiff (𝓡 3) (𝓡 3) ∞ f →
        Nonempty (M59LoopPostcomposition f)

  regular_postcomposition : ∀ {M N : Type u}
      [TopologicalSpace M] [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
      [TopologicalSpace N] [ChartedSpace LoopAmbient N] [IsManifold (𝓡 3) ∞ N]
      (f : ContinuousMap M N) (_smooth : ContMDiff (𝓡 3) (𝓡 3) ∞ f)
      (L : M59LoopPostcomposition f) (Gamma : FreeTwoSphereFamily (M := M)),
      ∃ Delta : FreeTwoSphereFamily (M := N),
        (∀ c, Delta.family c = L.map (Gamma.family c)) ∧
        Delta.class_certificate.sphere_parameter =
          Gamma.class_certificate.sphere_parameter ∧
        familySigmaClass Delta =
          ⟨f Gamma.basepoint,
            surgeryHomotopyMap (n := 2) L.map (L.maps_constant Gamma.basepoint)
              Gamma.homotopy_class⟩
  naturality : ∀ {M N : Type u}
      [TopologicalSpace M] [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
      [T2Space M] [SecondCountableTopology M]
      [TopologicalSpace N] [ChartedSpace LoopAmbient N] [IsManifold (𝓡 3) ∞ N]
      [T2Space N] [SecondCountableTopology N]
      (compactM : IsCompact (Set.univ : Set M))
      (connectedM : IsConnected (Set.univ : Set M))
      (compactN : IsCompact (Set.univ : Set N))
      (connectedN : IsConnected (Set.univ : Set N))
      (x : M) (y : N)
      (piTwoM : Subsingleton (HomotopyGroup.Pi 2 M x))
      (piTwoN : Subsingleton (HomotopyGroup.Pi 2 N y))
      (f : ContinuousMap M N) (_smooth : ContMDiff (𝓡 3) (𝓡 3) ∞ f)
      (based : f x = y)
      (L : M59LoopPostcomposition f)
      (alpha : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := M)) (constantC1Loop x)),
      (core compactN connectedN y piTwoN).pi_two_pi_three
        (surgeryHomotopyMap (n := 2) L.map (L.map_based based) alpha) =
      surgeryHomotopyMap (n := 3) f based
        ((core compactM connectedM x piTwoM).pi_two_pi_three alpha)
  relative_naturality : ∀ {M N : Type u}
      [TopologicalSpace M] [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
      [TopologicalSpace N] [ChartedSpace LoopAmbient N] [IsManifold (𝓡 3) ∞ N]
      (f : ContinuousMap M N) (L : M59LoopPostcomposition f)
      (x : M)
      (F G : ContinuousMap (Fin 2 → I) (C1FreeLoopSpace (M := M))),
      ContinuousMap.HomotopicWith F G (M59RelativeLoopCubeAt x) →
        ContinuousMap.HomotopicWith (L.map.comp F) (L.map.comp G)
          (M59RelativeLoopCubeAt (f x))

end PoincareConjecture
