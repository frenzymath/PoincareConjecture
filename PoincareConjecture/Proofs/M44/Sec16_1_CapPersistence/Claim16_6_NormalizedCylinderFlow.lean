import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_CylinderFlow
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_CoordinateTargetCoefficients

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M44

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {origin scale B : ℝ} {U : Set C.carrier}

theorem exists_normalized_cylinder_physical_flow
    (P : M44CapPersistencePredecessors.{u}) (hpinch : SurgeryFlowPinched F)
    (e : SurgeryFlowCylinder F C origin scale (Ico 0 B) U) (hU : IsOpen U) (hB : 0 < B)
    (f : PartialDiffeomorph (𝓡 3) (𝓡 3) E C.carrier ∞) (hmap : f.target ⊆ U) :
    ∃ G : RicciFlow 3 (⟨f.target, f.open_target⟩ : Opens C.carrier) (Ico 0 B),
      ∀ (p : (⟨f.target, f.open_target⟩ : Opens C.carrier)) (s : ℝ) (hs : s ∈ Ico 0 B),
        ∀ x ∈ f.source, ∀ v w : E,
          (G.metric s).pullbackCoefficients (targetChart f p) x v w =
            e.pullbackInner s hs (f x) (mfderiv (𝓡 3) (𝓡 3) f x v)
              (mfderiv (𝓡 3) (𝓡 3) f x w) := by
  obtain ⟨H0, hcoeff⟩ := exists_cylinder_coordinate_flow P hpinch e hU hB f hmap
  let H := coordinateFlowToTarget f H0
  have htime : origin < origin + B / scale := by linarith [div_pos hB e.scale_pos]
  let I : SpacetimeInterval := {
    domain := Ico origin (origin + B / scale)
    ordConnected := ordConnected_Ico
    nontrivial := (Ico_infinite htime).nontrivial }
  obtain ⟨R⟩ := P.ordinary_flow (⟨f.target, f.open_target⟩ : Opens C.carrier)
    I H scale e.scale_pos origin
  have hsub : Ico (0 : ℝ) B ⊆ (parabolicInterval scale e.scale_pos origin I).domain := by
    intro s hs
    apply (mem_parabolicInterval_iff scale e.scale_pos origin I s).mpr
    change origin ≤ origin + s / scale ∧ origin + s / scale < origin + B / scale
    exact ⟨le_add_of_nonneg_right (div_nonneg hs.1 e.scale_pos.le),
      by linarith [(div_lt_div_iff_of_pos_right e.scale_pos).mpr hs.2]⟩
  let G := Poincare.Geometry.RicciFlow.Harnack.restrictFlow R.flow hsub ordConnected_Ico
    (Ico_infinite hB).nontrivial
  refine ⟨G, ?_⟩
  intro p s hs x hx v w
  have htarget := coordinateFlowToTarget_pullbackCoefficients f H0 (origin + s / scale)
    (fun y => cylinderTimeCoefficients e f 0 ⟨le_rfl, hB⟩ (origin + s / scale, y))
    (hcoeff (origin + s / scale)) p hx
  rw [cylinderTimeCoefficients_at e f 0 ⟨le_rfl, hB⟩ s hs x] at htarget
  have hscaled : (G.metric s).pullbackCoefficients (targetChart f p) x v w =
      scale * (H.metric (origin + s / scale)).pullbackCoefficients (targetChart f p) x v w := by
    exact R.metric_eq s (targetChart f p x)
      (mfderiv (𝓡 3) (𝓡 3) (targetChart f p) x v)
      (mfderiv (𝓡 3) (𝓡 3) (targetChart f p) x w)
  rw [hscaled, htarget]
  exact cylinderPhysicalCoefficients_normalization e hU f.open_source f.contMDiffOn
    (fun _ hy => hmap (f.map_source hy)) s hs hx v w

end PoincareConjecture.M44
