import PoincareConjecture.Definitions.M61Width
import PoincareConjecture.Definitions.Ch19.RampEstimates

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

section LoopFamilies

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

structure M61FamilyWidthProperties (g : RiemannianMetric 3 M)
    (F : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))) : Prop where
  area_continuous : Continuous (fun c => fillingArea g (F c))
  bounded_above : BddAbove (Set.range (fun c => fillingArea g (F c)))
  attained : ∃ c, fillingArea g (F c) = m61FamilyWidth g F
  nonnegative : 0 ≤ m61FamilyWidth g F

structure M61FreeClassWidthProperties (g : RiemannianMetric 3 M)
    (F : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))) : Prop where
  nonempty : (m61FreeClassWidthRange g F).Nonempty
  bounded_below : BddBelow (m61FreeClassWidthRange g F)
  nonnegative : 0 ≤ m61FreeClassWidth g F
  le_member : ∀ G : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M)),
    M61NullFamily G → F.Homotopic G → m61FreeClassWidth g F ≤ m61FamilyWidth g G
  near_minimizer : ∀ epsilon : ℝ, 0 < epsilon →
    ∃ G : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M)),
      M61NullFamily G ∧ F.Homotopic G ∧
        m61FamilyWidth g G < m61FreeClassWidth g F + epsilon
  homotopy_invariant :
    ∀ G : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M)),
      M61NullFamily G → F.Homotopic G →
        m61FreeClassWidth g F = m61FreeClassWidth g G

def M61UniqueClassLabels (q : M59SphereQuotient) (x : M) : Prop :=
  ∀ F : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M)),
    M61NullFamily F →
      ∃! alpha : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := M)) (constantC1Loop x),
        M61Represents q x alpha F

structure M61BasedClassWidthProperties (q : M59SphereQuotient)
    (g : RiemannianMetric 3 M) (x : M)
    (alpha : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := M)) (constantC1Loop x)) :
    Prop where
  normalized_seed : ∃ Gamma : FreeTwoSphereFamily (M := M),
    M59NormalizedAt q x Gamma ∧ familySigmaClass Gamma = ⟨x, alpha⟩
  nonempty : (m61BasedClassWidthRange q g x alpha).Nonempty
  bounded_below : BddBelow (m61BasedClassWidthRange q g x alpha)
  nonnegative : 0 ≤ m61BasedClassWidth q g x alpha
  range_eq_free : ∀ F : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M)),
    M61NullFamily F → M61Represents q x alpha F →
      m61BasedClassWidthRange q g x alpha = m61FreeClassWidthRange g F
  eq_free : ∀ F : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M)),
    M61NullFamily F → M61Represents q x alpha F →
      m61BasedClassWidth q g x alpha = m61FreeClassWidth g F
  near_minimizer : ∀ epsilon : ℝ, 0 < epsilon →
    ∃ F : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M)),
      M61NullFamily F ∧ M61Represents q x alpha F ∧
        m61FamilyWidth g F < m61BasedClassWidth q g x alpha + epsilon

end LoopFamilies

structure M61RawWidthCore : Prop where
  family : ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
      [T2Space M] [SecondCountableTopology M] (g : RiemannianMetric 3 M),
    IsCompact (Set.univ : Set M) →
    ∀ F : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M)),
      M61NullFamily F → M61FamilyWidthProperties g F
  free_class : ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
      [T2Space M] [SecondCountableTopology M] (g : RiemannianMetric 3 M),
    IsCompact (Set.univ : Set M) →
    ∀ F : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M)),
      M61NullFamily F → M61FreeClassWidthProperties g F

structure M61SphereWidthProperties
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) : Prop where
  positive : 0 < m61SphereWidth g
  least : IsLeast (m61SphereAreaRange g) (m61SphereWidth g)
  attained : ∃ f : UnitTwoSphere → M, M60BranchedMinimalSphere g f ∧
    ¬ IsNullHomotopicSphere f ∧ m60SphereArea g f = m61SphereWidth g

def M61ShortFamilyWidthClaim : Prop :=
  ∀ {M : Type u} [TopologicalSpace M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    [T2Space M] [SecondCountableTopology M] (g : RiemannianMetric 3 M),
  IsCompact (Set.univ : Set M) → ∀ eta : ℝ, 0 < eta →
    ∃ zeta : ℝ, 0 < zeta ∧ zeta < eta / 2 ∧
      ∀ F : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M)),
        M61NullFamily F → (∀ c, freeLoopLength g (F c) < zeta) →
          m61FamilyWidth g F < eta

structure M61WidthTheory (q : M59SphereQuotient) : Prop extends M61RawWidthCore.{u} where
  class_labels : ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
      [T2Space M] [SecondCountableTopology M],
    IsCompact (Set.univ : Set M) → IsConnected (Set.univ : Set M) →
    ∀ x : M, Subsingleton (HomotopyGroup.Pi 2 M x) → M61UniqueClassLabels q x
  based_class : ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
      [T2Space M] [SecondCountableTopology M] (g : RiemannianMetric 3 M),
    IsCompact (Set.univ : Set M) → IsConnected (Set.univ : Set M) →
    ∀ x : M, Subsingleton (HomotopyGroup.Pi 2 M x) →
    ∀ alpha : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := M)) (constantC1Loop x),
      M61BasedClassWidthProperties q g x alpha
  sphere : ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
      [T2Space M] [SecondCountableTopology M] (g : RiemannianMetric n M),
    IsCompact (Set.univ : Set M) → ∀ x : M,
      Nontrivial (HomotopyGroup.Pi 2 M x) → M61SphereWidthProperties g
  short_family : M61ShortFamilyWidthClaim.{u}

end PoincareConjecture
