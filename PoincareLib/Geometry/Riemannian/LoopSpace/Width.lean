import PoincareLib.Topology.Homotopy.LoopSpace.Family
import PoincareLib.Geometry.Riemannian.LoopSpace.Area.Basic

/-!
# Filling-area width of sphere families

Adapted from Mapher commit f927d9e1f0810042766d3b5f64d3f4da02ee93cc.
Source: Morgan--Tian, Definition 18.17 and Lemma 18.27, pp. 430, 434-435.
-/

set_option autoImplicit false
open scoped Manifold ContDiff Bundle Topology ENNReal unitInterval
universe u
namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

/-- Width of a free family, as the supremum of its filling areas. -/
noncomputable def familyWidth (g : RiemannianMetric 3 M)
    (Γ : FreeTwoSphereFamily (M := M)) : ℝ :=
  sSup (Set.range (fun c => fillingArea g (Γ.family c)))

/-- The maximum and finiteness facts needed to use the supremum as a maximum. -/
structure FamilyWidthData (g : RiemannianMetric 3 M)
    (Γ : FreeTwoSphereFamily (M := M)) where
  filling_data : ∀ c, FillingAreaData g (Γ.family c)
  bounded_above : BddAbove (Set.range (fun c => fillingArea g (Γ.family c)))
  attained : ∃ c : LoopTwoSphere,
    fillingArea g (Γ.family c) = familyWidth g Γ

/-- The concrete set over which a free homotopy class width is minimized. -/
noncomputable def classWidthRange (g : RiemannianMetric 3 M)
    (ξ : FreeTwoSphereFamily (M := M)) : Set ℝ :=
  by classical
    exact {w | ∃ Γ : FreeTwoSphereFamily (M := M),
      familySigmaClass Γ = familySigmaClass ξ ∧
        Nonempty (FreeTwoSphereClassCertificate Γ.basepoint Γ.family
          Γ.homotopy_class) ∧
        FreeTwoSphereHomotopic ξ Γ ∧ familyWidth g Γ = w}

noncomputable def classWidth (g : RiemannianMetric 3 M)
    (ξ : FreeTwoSphereFamily (M := M)) : ℝ :=
  by classical
    exact sInf (classWidthRange g ξ)

/-- Boundedness and a finite witness for the class infimum. -/
structure ClassWidthData (g : RiemannianMetric 3 M)
    (ξ : FreeTwoSphereFamily (M := M)) where
  based_class : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := M))
    (constantC1Loop ξ.basepoint)
  based_class_eq : based_class = ξ.homotopy_class
  representative : FreeTwoSphereFamily (M := M)
  representative_based : representative.basepoint = ξ.basepoint
  representative_class : familySigmaClass representative = familySigmaClass ξ
  representative_homotopic : FreeTwoSphereHomotopic ξ representative
  representative_width_finite : ∃ C : ℝ, familyWidth g representative ≤ C
  bounded_below : BddBelow (classWidthRange g ξ)

end PoincareMT
