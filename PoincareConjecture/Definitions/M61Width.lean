import PoincareConjecture.Definitions.M59LoopIdentification
import PoincareConjecture.Definitions.M60MinimalSpheres
import PoincareConjecture.Definitions.M53SphereSeparation

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

section LoopFamilies

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

def M61NullFamily (F : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))) :
    Prop :=
  ∀ c, IsNullHomotopicLoop (F c)

noncomputable def m61FamilyWidth (g : RiemannianMetric 3 M)
    (F : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))) : ℝ :=
  sSup (Set.range (fun c => fillingArea g (F c)))

def m61FreeClassWidthRange (g : RiemannianMetric 3 M)
    (F : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))) : Set ℝ :=
  {w | ∃ G : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M)),
    M61NullFamily G ∧ F.Homotopic G ∧ m61FamilyWidth g G = w}

noncomputable def m61FreeClassWidth (g : RiemannianMetric 3 M)
    (F : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))) : ℝ :=
  sInf (m61FreeClassWidthRange g F)

def M61Represents (q : M59SphereQuotient) (x : M)
    (alpha : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := M)) (constantC1Loop x))
    (F : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))) : Prop :=
  ∃ Gamma : FreeTwoSphereFamily (M := M),
    M59NormalizedAt q x Gamma ∧ familySigmaClass Gamma = ⟨x, alpha⟩ ∧
      F.Homotopic (m59FamilyMap Gamma)

def m61BasedClassWidthRange (q : M59SphereQuotient) (g : RiemannianMetric 3 M)
    (x : M)
    (alpha : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := M)) (constantC1Loop x)) :
    Set ℝ :=
  {w | ∃ F : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M)),
    M61NullFamily F ∧ M61Represents q x alpha F ∧ m61FamilyWidth g F = w}

noncomputable def m61BasedClassWidth (q : M59SphereQuotient)
    (g : RiemannianMetric 3 M) (x : M)
    (alpha : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := M)) (constantC1Loop x)) : ℝ :=
  sInf (m61BasedClassWidthRange q g x alpha)

end LoopFamilies

section Spheres

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

def m61SphereAreaRange (g : RiemannianMetric n M) : Set ℝ :=
  {a | ∃ f : UnitTwoSphere → M, ContMDiff (𝓡 2) (𝓡 n) 1 f ∧
    ¬ IsNullHomotopicSphere f ∧ m60SphereArea g f = a}

noncomputable def m61SphereWidth (g : RiemannianMetric n M) : ℝ :=
  sInf (m61SphereAreaRange g)

end Spheres

end PoincareConjecture
