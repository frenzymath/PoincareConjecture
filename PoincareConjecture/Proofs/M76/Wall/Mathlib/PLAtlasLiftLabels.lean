import PoincareConjecture.Proofs.M76.Wall.Mathlib.PLAtlasSignCover
import Mathlib.Topology.LocallyConstant.Basic

set_option autoImplicit false

open Set Topology

namespace Geometry

variable {X Y E ι : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_plAtlasSign_lift_labels
    (e : ι → OpenPartialHomeomorph X E)
    (hcover : ∀ x : X, ∃ i, x ∈ (e i).source)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid E)
    (U : Set X) (f : C(Y, U))
    (L : C(Y, (plAtlasSignCore e hcover hcompat U).TotalSpace))
    (hL : ∀ y, (plAtlasSignCore e hcover hcompat U).proj (L y) = f y) :
    let Z := plAtlasSignCore e hcover hcompat U
    let V : ι → Set Y := fun i => {y | (f y : X) ∈ (e i).source}
    (∀ i, IsOpen (V i)) ∧
      ∃ label : ∀ i, LocallyConstant (V i) PLOrientationSheet,
        (∀ i y, label i y = ((Z.localTriv i) (L y)).2) ∧
        ∀ i j y (hi : y ∈ V i) (hj : y ∈ V j),
          (label j ⟨y, hj⟩).val =
            plAtlasTransitionSign e hcompat i j ⟨f y, hi, hj⟩ *
              (label i ⟨y, hi⟩).val := by
  let Z := plAtlasSignCore e hcover hcompat U
  let V : ι → Set Y := fun i => {y | (f y : X) ∈ (e i).source}
  have hV (i : ι) : IsOpen (V i) :=
    (e i).open_source.preimage (continuous_subtype_val.comp f.continuous)
  have hsource (i : ι) (y : Y) (hy : y ∈ V i) : L y ∈ (Z.localTriv i).source := by
    change (Z.proj (L y) : X) ∈ (e i).source
    rw [hL y]
    exact hy
  have hcontinuous (i : ι) :
      Continuous (fun y : V i => ((Z.localTriv i) (L y)).2) :=
    ((Z.localTriv i).continuousOn.comp_continuous
      (L.continuous.comp continuous_subtype_val) (fun y => hsource i y y.property)).snd
  let label (i : ι) : LocallyConstant (V i) PLOrientationSheet :=
    ⟨fun y => ((Z.localTriv i) (L y)).2,
      (IsLocallyConstant.iff_continuous _).mpr (hcontinuous i)⟩
  refine ⟨hV, label, (fun _ _ => rfl), ?_⟩
  intro i j y hi hj
  have hpair : (f y, ((Z.localTriv i) (L y)).2) = (Z.localTriv i) (L y) := by
    apply Prod.ext
    · change f y = Z.proj (L y)
      exact (hL y).symm
    · rfl
  have hinverse : (Z.localTriv i).toOpenPartialHomeomorph.symm
      (f y, ((Z.localTriv i) (L y)).2) = L y := by
    rw [hpair]
    exact (Z.localTriv i).toOpenPartialHomeomorph.left_inv (hsource i y hi)
  have hchange := plAtlasSignCore_localTriv_change e hcover hcompat U i j
    (f y) hi hj (((Z.localTriv i) (L y)).2)
  dsimp only at hchange
  rw [hinverse] at hchange
  exact hchange.2

end Geometry
