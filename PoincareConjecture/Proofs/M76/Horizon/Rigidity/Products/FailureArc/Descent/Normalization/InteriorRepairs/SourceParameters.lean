import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.Source.EmbeddedCharts
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.Source.ClippedParameters

set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "A" => (ℝ × ℝ)

theorem exists_planar_interior_source_parameters (S : Set A) (z : S) :
    ∃ (q : OpenPartialHomeomorph S V2) (F : A → V2),
      q.source = Subtype.val ⁻¹' interior S ∧
      (∀ x : S, q x = F x) ∧
      LocallyPiecewiseAffineOn F (interior S) ∧
      LocallyPiecewiseAffineOn (fun v => (q.symm v : A)) q.target := by
  classical
  let c := ContinuousLinearEquiv.finTwoArrow ℝ ℝ
  let g : V2 → S := fun v => if hv : c v ∈ S then ⟨c v, hv⟩ else z
  have hgv (v : V2) (hv : c v ∈ interior S) : (g v : A) = c v := by
    simp only [g, dif_pos (interior_subset hv)]
  let q : OpenPartialHomeomorph S V2 :=
    { toFun := fun x => c.symm x
      invFun := g
      source := Subtype.val ⁻¹' interior S
      target := c ⁻¹' interior S
      map_source' := by intro x hx; simpa only [mem_preimage, c.apply_symm_apply] using hx
      map_target' := by intro v hv; change (g v : A) ∈ interior S; rwa [hgv v hv]
      left_inv' := by
        intro x hx
        apply Subtype.ext
        rw [hgv _ (by simpa only [mem_preimage, c.apply_symm_apply] using hx), c.apply_symm_apply]
      right_inv' := by
        intro v hv
        rw [hgv v hv, c.symm_apply_apply]
      continuousOn_toFun := (c.symm.continuous.comp continuous_subtype_val).continuousOn
      continuousOn_invFun := by
        apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
        apply c.continuous.continuousOn.congr
        intro v hv
        exact hgv v hv
      open_source := isOpen_interior.preimage continuous_subtype_val
      open_target := isOpen_interior.preimage c.continuous }
  refine ⟨q, c.symm, rfl, fun _ => rfl, ?_, ?_⟩
  · exact locallyPiecewiseAffineOn_affine c.symm.toContinuousLinearMap.toContinuousAffineMap
      isOpen_interior
  · apply (locallyPiecewiseAffineOn_affine c.toContinuousLinearMap.toContinuousAffineMap
      q.open_target).congr
    intro v hv
    exact (hgv v hv).symm

theorem exists_embedded_planar_interior_chart
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)}
    (K : SimplicialComplex ℝ A) (hK : K.faces.Finite)
    {f : A → X} (hf : PolyhedralPLInCharts e f K.space)
    (hemb : IsEmbedding (fun x : K.space => f x))
    (G : OpenPartialHomeomorph X (Fin 3 → ℝ))
    (hcompat : ∀ i, (e i).symm.trans G ∈ piecewiseAffineGroupoid (Fin 3 → ℝ))
    (z : K.space) (hz : (z : A) ∈ interior K.space) (hzG : f z ∈ G.source)
    {W : Set X} (hW : IsOpen W) (hzW : f z ∈ W) :
    ∃ H : OpenPartialHomeomorph X ((ℝ × ℝ) × ℝ),
      f z ∈ H.source ∧ H.source ⊆ W ∩ G.source ∧
      H.target = interior (CoordinateHalfBoxes.box 1) ∧ H (f z) = 0 ∧
      (∀ x ∈ H.source, x ∈ f '' K.space ↔ (H x).2 = 0) ∧
      ∀ i,
        LocallyPiecewiseAffineOn ((e i).symm.trans H) ((e i).symm.trans H).source ∧
        LocallyPiecewiseAffineOn (H.symm.trans (e i)) (H.symm.trans (e i)).source := by
  obtain ⟨q, F, hqs, _, _, hqi⟩ := exists_planar_interior_source_parameters K.space z
  exact exists_embedded_source_plane_chart K hK hf hemb G hcompat z hzG q
    (hqs.symm.subset hz) hqi hW hzW

end PoincareConjecture.M76.Dehn
