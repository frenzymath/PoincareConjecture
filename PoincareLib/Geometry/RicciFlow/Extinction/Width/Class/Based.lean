import PoincareLib.Geometry.RicciFlow.Extinction.Width.Class.Identification
import PoincareLib.Geometry.RicciFlow.Extinction.Width.Class.MinimalSphere
import PoincareLib.Topology.Manifold.EmbeddedSphere.Basic

/-!
# M61 actual free-family and sphere-area infima

Morgan--Tian Definition 18.17, p. 430, ranges over all continuous sphere
families of null C1 loops. The based representation relation below labels
those raw competitors; it does not require them to be normalized families.
The separate sphere infimum is Lemma 18.10, pp. 424-426. See
`reviews/contracts/M61-round1.md` for the source and legacy-width distinction.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT

section LoopFamilies

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

/-- A property of the displayed continuous family, with no based condition. -/
def M61NullFamily (F : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))) :
    Prop :=
  ∀ c, IsNullHomotopicLoop (F c)

/-- The actual supremum of the filling areas in a continuous sphere family. -/
noncomputable def m61FamilyWidth (g : RiemannianMetric 3 M)
    (F : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))) : ℝ :=
  sSup (Set.range (fun c => fillingArea g (F c)))

/-- All raw null families in the same free homotopy class as the anchor. -/
def m61FreeClassWidthRange (g : RiemannianMetric 3 M)
    (F : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))) : Set ℝ :=
  {w | ∃ G : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M)),
    M61NullFamily G ∧ F.Homotopic G ∧ m61FamilyWidth g G = w}

/-- Definition 18.17's infimum over all free representatives. -/
noncomputable def m61FreeClassWidth (g : RiemannianMetric 3 M)
    (F : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))) : ℝ :=
  sInf (m61FreeClassWidthRange g F)

/-- A normalized seed labels a raw free family at the fixed quotient and point.
The raw family itself has no constant-member or extra-regularity condition. -/
def M61Represents (q : M59SphereQuotient) (x : M)
    (alpha : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := M)) (constantC1Loop x))
    (F : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))) : Prop :=
  ∃ Gamma : FreeTwoSphereFamily (M := M),
    M59NormalizedAt q x Gamma ∧ familySigmaClass Gamma = ⟨x, alpha⟩ ∧
      F.Homotopic (m59FamilyMap Gamma)

/-- Every raw null representative of the specified based class is admissible. -/
def m61BasedClassWidthRange (q : M59SphereQuotient) (g : RiemannianMetric 3 M)
    (x : M)
    (alpha : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := M)) (constantC1Loop x)) :
    Set ℝ :=
  {w | ∃ F : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M)),
    M61NullFamily F ∧ M61Represents q x alpha F ∧ m61FamilyWidth g F = w}

/-- The based notation for the same unrestricted free-class infimum. -/
noncomputable def m61BasedClassWidth (q : M59SphereQuotient)
    (g : RiemannianMetric 3 M) (x : M)
    (alpha : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := M)) (constantC1Loop x)) : ℝ :=
  sInf (m61BasedClassWidthRange q g x alpha)

end LoopFamilies

section Spheres

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- Areas of all C1 non-null sphere maps, across all nontrivial free classes. -/
def m61SphereAreaRange (g : RiemannianMetric n M) : Set ℝ :=
  {a | ∃ f : UnitTwoSphere → M, ContMDiff (𝓡 2) (𝓡 n) 1 f ∧
    ¬ IsNullHomotopicSphere f ∧ m60SphereArea g f = a}

/-- The least-sphere invariant W2, distinct from the loop-family width. -/
noncomputable def m61SphereWidth (g : RiemannianMetric n M) : ℝ :=
  sInf (m61SphereAreaRange g)

end Spheres

end PoincareMT
