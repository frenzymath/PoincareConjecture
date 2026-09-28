import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLInverseChart

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

variable {X E F ι : Type*} [TopologicalSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_original_PL_embedded_inverse
    (e : ι → OpenPartialHomeomorph X F)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid F)
    {c : E → X} {S : Set E} {V : Set X}
    (hc : PolyhedralPLInCharts e c S)
    (hi : Topology.IsEmbedding (fun z : S => c z))
    (hV : IsOpen V) (hVS : V ⊆ c '' S) :
    ∃ q : X → E, Set.LeftInvOn q c S ∧ ContinuousOn q V ∧
      MapsTo q V S ∧ (∀ x ∈ V, c (q x) = x) ∧
      (∀ i, LocallyPiecewiseAffineOn (q ∘ (e i).symm)
        ((e i).target ∩ (e i).symm ⁻¹' V)) := by
  classical
  let R := Set.range (fun z : S => c z)
  let q : X → E := fun x => if h : x ∈ R then
    (hi.toHomeomorph.symm ⟨x, h⟩ : E) else 0
  have hqval (x : R) : q x = (hi.toHomeomorph.symm x : E) := by
    simp only [q, dif_pos x.property]
    rfl
  have hqleft : Set.LeftInvOn q c S := by
    intro z hz
    have hm : c z ∈ R := ⟨⟨z, hz⟩, rfl⟩
    rw [show q (c z) = (hi.toHomeomorph.symm ⟨c z, hm⟩ : E) from hqval ⟨c z, hm⟩]
    exact congrArg Subtype.val (hi.toHomeomorph.symm_apply_apply ⟨z, hz⟩)
  have hVR : V ⊆ R := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := hVS hx
    exact ⟨⟨z, hz⟩, rfl⟩
  have hqcR : ContinuousOn q R := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact (continuous_subtype_val.comp hi.toHomeomorph.symm.continuous).congr
      (fun x => (hqval x).symm)
  have hqS : MapsTo q V S := by
    intro x hx
    rw [hqval ⟨x, hVR hx⟩]
    exact (hi.toHomeomorph.symm ⟨x, hVR hx⟩).property
  have hright (x : X) (hx : x ∈ V) : c (q x) = x := by
    obtain ⟨z, hz, rfl⟩ := hVS hx
    rw [hqleft hz]
  refine ⟨q, hqleft, hqcR.mono hVR, hqS, hright, ?_⟩
  intro i
  let T := (e i).target ∩ (e i).symm ⁻¹' V
  have hT : IsOpen T :=
    (e i).symm.continuousOn.isOpen_inter_preimage (e i).open_target hV
  apply hc.locallyPiecewiseAffineOn_inverse_comp
    (fun x hx y hy h => congrArg Subtype.val (hi.injective (show
      (fun z : S => c z) ⟨x, hx⟩ = (fun z : S => c z) ⟨y, hy⟩ from h)))
    (e i) (hcompat i) (g := id)
    (locallyPiecewiseAffineOn_affine (ContinuousAffineMap.id ℝ F) hT)
  · exact (hqcR.mono hVR).comp ((e i).symm.continuousOn.mono inter_subset_left)
      (fun _ hy => hy.2)
  · exact fun _ hy => hqS hy.2
  · exact fun _ hy => hy.1
  · exact fun y hy => hright ((e i).symm y) hy.2

end PoincareConjecture.M76
