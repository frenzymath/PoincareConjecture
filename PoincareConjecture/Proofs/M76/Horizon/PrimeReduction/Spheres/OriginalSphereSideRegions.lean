import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.OriginalSphereNormalOrientation
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.Topology
import PoincareConjecture.Proofs.M76.Brown.AmbientSideRegions

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

private noncomputable def sideNormalCoordinates : V3 ≃ₜ C3 :=
  let L : V3 ≃ₗ[ℝ] C3 :=
    { toFun := fun x => ((x 1, x 2), x 0)
      invFun := fun z => ![z.2, z.1.1, z.1.2]
      left_inv := by intro x; funext i; fin_cases i <;> rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  L.toContinuousLinearEquiv.toHomeomorph

theorem ChartwisePLSphere.exists_side_regions
    {X ι : Type*} [MetricSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (hcover : ∀ x ∈ S, ∃ i, x ∈ (e i).source) :
    ∃ W Rpos Rneg : Set X, IsOpen W ∧ S ⊆ W ∧
      Rpos ∪ Rneg = W ∧ Rpos ∩ Rneg = S ∧
      IsClosed ((Subtype.val : W → X) ⁻¹' Rpos) ∧
      IsClosed ((Subtype.val : W → X) ⁻¹' Rneg) ∧
      ∀ x ∈ S, ∃ B : OpenPartialHomeomorph X V3,
        x ∈ B.source ∧ B.source ⊆ W ∧
        (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
        ∀ y ∈ B.source,
          (y ∈ S ↔ (B y) 0 = 0) ∧
          (y ∈ Rpos ↔ 0 ≤ (B y) 0) ∧
          (y ∈ Rneg ↔ (B y) 0 ≤ 0) := by
  obtain ⟨B, hxB, hBS, hB, hagree⟩ :=
    s.exists_coherently_oriented_pair_charts hcompat hcover
  let E := fun x => (B x).transHomeomorph sideNormalCoordinates
  have hEcover (x : S) : (x : X) ∈ (E x).source := hxB x
  have hEpair (i : S) (y : X) (hy : y ∈ (E i).source) :
      y ∈ S ↔ (E i y).2 = 0 := hBS i y hy
  have hEgerm (i j : S) (x : S)
      (hx : (x : X) ∈ (E i).source ∩ (E j).source) :
      ∃ V : Set X, IsOpen V ∧ (x : X) ∈ V ∧
        EqOn (fun y => SignType.sign (E i y).2)
          (fun y => SignType.sign (E j y).2) V := by
    obtain ⟨V, hV, hxV, _, heq⟩ := hagree i j x hx
    exact ⟨V, hV, hxV, heq⟩
  obtain ⟨W, Rp, Rn, hW, hSW, hu, hi, hpc, hnc, hlocal⟩ :=
    BrownCollar.exists_ambient_side_regions s.isCompact E hEcover hEpair hEgerm
  refine ⟨W, Rp, Rn, hW, hSW, hu, hi, hpc, hnc, ?_⟩
  intro x hx
  obtain ⟨i, V, hV, hxV, hVB, hVW, hside⟩ := hlocal ⟨x, hx⟩
  let C := (B i).restrOpen V hV
  have hCB : C.source ⊆ (B i).source := inter_subset_left
  refine ⟨C, ⟨hVB hxV, hxV⟩, inter_subset_right.trans hVW, ?_, ?_⟩
  · intro j
    exact ⟨(hB j i).1.mono ((e j).symm.trans C).open_source
      (fun z hz => ⟨hz.1, hz.2.1⟩),
      (hB j i).2.mono ((e j).symm.trans C).symm.open_source
        (fun z hz => ⟨hz.1.1, hz.2⟩)⟩
  · intro y hy
    exact ⟨hBS i y (hCB hy), hside y hy.2⟩

end PoincareConjecture.M76
