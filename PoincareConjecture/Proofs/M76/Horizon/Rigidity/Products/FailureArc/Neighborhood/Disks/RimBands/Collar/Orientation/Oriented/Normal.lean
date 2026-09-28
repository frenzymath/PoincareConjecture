import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Collar.Orientation.Oriented.AmbientLabels
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Collar.Orientation.Charts.TangentialAtlas
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Collar.Orientation.GlobalSurfaceLabels
import PoincareConjecture.Proofs.M76.Brown.OrientedFlatteningCharts







set_option autoImplicit false

open Poincare.Topology.Orientation.ProjectivePlane
open Set Geometry

namespace PoincareConjecture.M76.Dehn.Annuli.RimBands

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)

theorem exists_original_planar_surface_normal_units_of_localOrientation
    {X : Type} {ι : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (O : LocalOrientation X) {S : Set X} [Nonempty S]
    (A : BrownCollar.FlatteningAtlas P2 S ι)
    (hPL : ∀ i j, A.transition i j ∈ piecewiseAffineGroupoid C3)
    (b : OpenPartialHomeomorph S P2) (hb : b.source = univ)
    (hbPL : ∀ i, (atlasTangentialChart A i).symm.trans b ∈ piecewiseAffineGroupoid P2) :
    ∃ a : ι → S → SignTypeˣ,
      (∀ i, ContinuousOn (a i) (A.baseSet i)) ∧
      ∀ i j x, x ∈ A.baseSet i ∩ A.baseSet j →
        a j x = A.transitionUnit i j x * a i x := by
  obtain ⟨ambient, hamb⟩ := exists_ambient_labels_of_localOrientation O A hPL
  obtain ⟨label, hlabel⟩ := exists_plAtlas_labels_of_global_chart (atlasTangentialChart A)
    (fun i j => atlasTangentialChart_compatible A i j (hPL i j)) b hb hbPL
  let tangent (i : ι) : LocallyConstant (A.baseSet i) SignTypeˣ :=
    LocallyConstant.map (fun s => Units.mk0 s.val s.property) (label i)
  have htan : ∀ i j (x : S) (hi : x ∈ A.baseSet i) (hj : x ∈ A.baseSet j),
      (tangent j ⟨x, hj⟩ : SignType) =
        plLocalSign (atlasTangentialTransition A i j)
          (tangentialTransition_mem_piecewiseAffineGroupoid _ (hPL i j) _)
          ⟨A.coordinate i x, A.transition_mem_source i j x ⟨hi, hj⟩⟩ *
            (tangent i ⟨x, hi⟩ : SignType) := by
    intro i j x hi hj
    exact (hlabel i j x hi hj).trans
      (congrArg (fun s => s * (tangent i ⟨x, hi⟩ : SignType))
        (atlasTangentialChart_transitionSign A hPL i j x ⟨hi, hj⟩))
  obtain ⟨a, ha, _, hcompat⟩ :=
    exists_normal_units_of_orientation_labels A hPL ambient tangent hamb htan
  exact ⟨a, ha, hcompat⟩



theorem exists_original_planar_surface_cooriented_charts_of_localOrientation
    {X : Type} {ι : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (O : LocalOrientation X) {S : Set X} [Nonempty S]
    (A : BrownCollar.FlatteningAtlas P2 S ι)
    (hPL : ∀ i j, A.transition i j ∈ piecewiseAffineGroupoid C3)
    (b : OpenPartialHomeomorph S P2) (hb : b.source = univ)
    (hbPL : ∀ i, (atlasTangentialChart A i).symm.trans b ∈ piecewiseAffineGroupoid P2) :
    ∃ E : S → OpenPartialHomeomorph X C3,
      (∀ x : S, (x : X) ∈ (E x).source) ∧
      (∀ i y, y ∈ (E i).source → (y ∈ S ↔ (E i y).2 = 0)) ∧
      ∀ i j (x : S), (x : X) ∈ (E i).source ∩ (E j).source →
        ∃ V : Set X, IsOpen V ∧ (x : X) ∈ V ∧
          EqOn (fun y => SignType.sign (E i y).2) (fun y => SignType.sign (E j y).2) V := by
  obtain ⟨a, ha, hcompat⟩ := exists_original_planar_surface_normal_units_of_localOrientation O A hPL b hb hbPL
  exact A.exists_oriented_charts a ha hcompat

end PoincareConjecture.M76.Dehn.Annuli.RimBands
