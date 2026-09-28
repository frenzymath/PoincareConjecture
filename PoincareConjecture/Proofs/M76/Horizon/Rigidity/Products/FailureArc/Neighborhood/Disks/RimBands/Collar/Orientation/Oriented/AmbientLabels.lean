import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Collar.Orientation.OrientedNormal
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Orientation.LocalProjection







set_option autoImplicit false

open Poincare.Topology.Orientation.ProjectivePlane
open Set Geometry

namespace PoincareConjecture.M76.Dehn.Annuli.RimBands

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem exists_ambient_labels_of_localOrientation
    {X : Type} {ι : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (O : LocalOrientation X) {S : Set X}
    (A : BrownCollar.FlatteningAtlas P2 S ι)
    (hPL : ∀ i j, A.transition i j ∈ piecewiseAffineGroupoid C3) :
    ∃ ambient : ∀ i, LocallyConstant (A.baseSet i) SignTypeˣ,
      ∀ i j (x : S) (hi : x ∈ A.baseSet i) (hj : x ∈ A.baseSet j),
        (ambient j ⟨x, hj⟩ : SignType) =
          plLocalSign (A.transition i j) (hPL i j)
            ⟨(A.coordinate i x, 0), A.transition_mem_source i j x ⟨hi, hj⟩⟩ *
              (ambient i ⟨x, hi⟩ : SignType) := by
  let L : C3 ≃ᴬ[ℝ] E3 :=
    (ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod]) :
      C3 ≃L[ℝ] E3).toContinuousAffineEquiv
  let q := fun i => (A.chart i).transHomeomorph L.toHomeomorph
  have hq := affine_model_plAtlas_compatible A.chart hPL L
  obtain ⟨label, hlabel⟩ := exists_plAtlas_labels_of_localOrientation O euclideanLocalOrientation q hq
  let pull (i : ι) : C(A.baseSet i, (q i).source) :=
    ⟨fun x => ⟨x.val.val, x.property⟩,
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
  let ambient (i : ι) := LocallyConstant.map (fun s => Units.mk0 s.val s.property)
    (LocallyConstant.comap (pull i) (label i))
  refine ⟨ambient, ?_⟩
  intro i j x hi hj
  have h := hlabel i j x hi hj
  have hsign : plAtlasTransitionSign q hq i j ⟨x, hi, hj⟩ =
      plAtlasTransitionSign A.chart hPL i j ⟨x, hi, hj⟩ :=
    plAtlasTransitionSign_affine_model A.chart hPL L i j ⟨x, hi, hj⟩
  rw [hsign] at h
  have hp :
      (⟨A.chart i x, by
        refine ⟨(A.chart i).map_source hi, ?_⟩
        change (A.chart i).symm (A.chart i x) ∈ (A.chart j).source
        rwa [(A.chart i).left_inv hi]⟩ : (A.transition i j).source) =
      ⟨(A.coordinate i x, 0), A.transition_mem_source i j x ⟨hi, hj⟩⟩ :=
    Subtype.ext (A.base_coordinate i x hi).symm
  change (ambient j ⟨x, hj⟩ : SignType) =
    plLocalSign (A.transition i j) (hPL i j) _ * (ambient i ⟨x, hi⟩ : SignType) at h
  exact h.trans (congrArg
    (fun z => plLocalSign (A.transition i j) (hPL i j) z *
      (ambient i ⟨x, hi⟩ : SignType)) hp)

end PoincareConjecture.M76.Dehn.Annuli.RimBands
