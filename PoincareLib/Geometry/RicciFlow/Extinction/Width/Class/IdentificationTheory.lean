import PoincareLib.Geometry.RicciFlow.Extinction.Width.Class.Identification
import PoincareLib.Geometry.RicciFlow.Surgery.Comparison.Basic

/-!
# M59 coherent loop-class identification

For a compact connected smooth three-manifold with trivial based pi2, the
identity component of the C1 free-loop space consists of its null loops and
its based pi2 is isomorphic to pi3 of the manifold. The same chosen comparison
is used for regular representatives and for every smooth based map.

Source: Morgan--Tian Claim 18.16 and Definition 18.17, printed p. 430;
`references/derived/MT2007.txt:21046-21110`. The absolute/relative square
comparison uses the pair from `references/derived/PerelmanIII.txt:34-40`.
Regularization and naturality are supporting conclusions for these concrete
models, not separate admissions or width estimates.

The free/based identification uses the closed three-manifold hypotheses and
the trivial deck action on pi3. It is not inferred from pi2-vanishing on an
arbitrary space. Hatcher, Algebraic Topology, Proposition 4A.2 (p. 422) and
Theorem 2C.3 (p. 179), supply the free-class and fixed-point inputs described
in `reviews/contracts/M59-round1.md`. Raw free homotopy is stated independently
of the decorated relation, which already includes equality of based classes.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology ENNReal unitInterval

universe u

namespace PoincareMT

section Carrier

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

/-- The loop-class conclusions on one manifold and one chosen point.
The system below supplies this data under explicit primitive hypotheses. -/
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
  /-- Upgrade raw homotopy to a path through regular family records, retaining
      the original endpoint records required by the existing width interface. -/
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

/-- One coherent choice across all carriers in the universe. Compactness,
connectedness, pi2-vanishing and smoothness are explicit primitive inputs;
the complete M59 theorem returns the existence of this system. -/
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
  /-- Smooth postcomposition preserves the actual regular family, its common
      sphere parameter and the class induced by the same continuous loop map. -/
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

end PoincareMT
