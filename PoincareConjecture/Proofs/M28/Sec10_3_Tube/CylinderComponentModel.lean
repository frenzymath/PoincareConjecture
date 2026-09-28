import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderSphereModel
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderTailModel
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderComponentSide









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.OpenCylinderModel

open M28

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {U : TopologicalSpace.Opens M}

private theorem inverse_height_readout (T : OpenCylinderModel (U : Set M)) (x : U) :
    ((T.homeomorph.symm x).2 : ℝ) = (T.inverse x).2 := by
  have hcoord : T.coordinate
      ((T.homeomorph.symm x).1, ((T.homeomorph.symm x).2 : ℝ)) = x := by
    rw [← T.coordinate_eq]
    exact congrArg Subtype.val (T.homeomorph.apply_symm_apply x)
  have hh := T.left_inverse
    (show ((T.homeomorph.symm x).1, ((T.homeomorph.symm x).2 : ℝ)) ∈
      univ ×ˢ Ioo (0 : ℝ) 1 from ⟨mem_univ _, (T.homeomorph.symm x).2.property⟩)
  rw [hcoord] at hh
  exact (congrArg Prod.snd hh).symm




theorem exists_oriented_model_of_component
    (T : OpenCylinderModel (U : Set M)) {S P : Set M}
    (hS : SmoothSphereIsotopicIn (U : Set M) S T.middleSphere)
    (hP : IsConnected P) (hPU : P ⊆ (U : Set M) \ S)
    (hcomponent : ∀ x ∈ P, connectedComponentIn Sᶜ x = P) :
    ∃ T' : OpenCylinderModel (U : Set M),
      T'.middleSphere = S ∧ P = T'.tail true (1 / 2) := by
  obtain ⟨A, hA⟩ := T.exists_isotopic_sphere_model hS
  have hzero (x : U) : cylinderSignedHeight A.homeomorph.symm x = 0 ↔ x.val ∈ S := by
    rw [cylinderSignedHeight, inverse_height_readout, sub_eq_zero]
    exact (A.mem_middleSphere_iff x.property).symm.trans (by rw [hA])
  have hrelative (x : M) (hx : x ∈ P) :
      connectedComponentIn ((U : Set M) \ S) x = P := by
    apply Subset.antisymm
    · exact (connectedComponentIn_mono x (fun _ hy => hy.2)).trans_eq (hcomponent x hx)
    · exact hP.isPreconnected.subset_connectedComponentIn hx hPU
  rcases cylinderSignedHeight_component_half A.homeomorph.symm hzero hP hPU hrelative
    with hn | hp
  · obtain ⟨R, _hc, hv, hm⟩ := A.exists_reflected_model
    refine ⟨R, hm.trans hA, ?_⟩
    have hhalf (x : U) : (1 / 2 : ℝ) < (R.inverse x).2 ↔ x.val ∈ P := by
      have hh : (A.inverse x).2 < 1 / 2 ↔ x.val ∈ P := by
        have hh := hn x
        change ((A.homeomorph.symm x).2 : ℝ) - 1 / 2 < 0 ↔ x.val ∈ P at hh
        rwa [inverse_height_readout A x, sub_neg] at hh
      rw [hv]
      change 1 / 2 < 1 - (A.inverse x).2 ↔ x.val ∈ P
      exact (by constructor <;> intro h <;> linarith :
        (1 / 2 : ℝ) < 1 - (A.inverse x).2 ↔ (A.inverse x).2 < 1 / 2).trans hh
    ext x
    rw [R.mem_tail_iff_m28 true (by norm_num) (by norm_num)]
    exact ⟨fun hx => ⟨(hPU hx).1, (hhalf ⟨x, (hPU hx).1⟩).mpr hx⟩,
      fun hx => (hhalf ⟨x, hx.1⟩).mp hx.2⟩
  · refine ⟨A, hA, ?_⟩
    have hhalf (x : U) : (1 / 2 : ℝ) < (A.inverse x).2 ↔ x.val ∈ P := by
      have hh := hp x
      change 0 < ((A.homeomorph.symm x).2 : ℝ) - 1 / 2 ↔ x.val ∈ P at hh
      rwa [inverse_height_readout A x, sub_pos] at hh
    ext x
    rw [A.mem_tail_iff_m28 true (by norm_num) (by norm_num)]
    exact ⟨fun hx => ⟨(hPU hx).1, (hhalf ⟨x, (hPU hx).1⟩).mpr hx⟩,
      fun hx => (hhalf ⟨x, hx.1⟩).mp hx.2⟩

end PoincareConjecture.OpenCylinderModel
