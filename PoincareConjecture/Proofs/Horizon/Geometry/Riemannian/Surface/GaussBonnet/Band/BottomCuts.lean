import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.CapBandRays







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology Manifold ContDiff Bundle
open Poincare.Topology.Plane.Curves

namespace PoincareConjecture.Topology.Surface.ObliqueBandFaces

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M}
  {lo : ℝ → ℝ} {a b ua wa ub wb ra rb : ℝ}
  (B : ObliqueBandFaces F lo a b ua wa ub wb ra rb)

theorem lowerArc_eq_normalized_bottom :
    B.lowerArc = (fun t => B.coordinates (collarParameterEquiv.symm (t, 0))) ''
      Icc (0 : ℝ) 1 := by
  have hab : a ≤ b := by
    simpa only [B.cuts.A_zero, B.cuts.B_zero] using (B.cuts.separated 0
      ⟨by linarith [B.cuts.radius_pos], B.cuts.radius_pos⟩).le
  have hi : (fun t : ℝ => a + t * (b - a)) '' Icc (0 : ℝ) 1 = Icc a b := by
    simpa using
      ((continuous_const : Continuous (fun _ : ℝ => a)).add
        (continuous_id.mul_const (b - a))).continuousOn.image_Icc_of_monotoneOn
        (zero_le_one : (0 : ℝ) ≤ 1) (fun x _ y _ hxy =>
          add_le_add_right (mul_le_mul_of_nonneg_right hxy (sub_nonneg.mpr hab)) a)
  rw [lowerArc, ← hi, image_image]
  exact image_congr (fun t _ => (B.coordinates_bottom t).symm)

theorem eq_endpoint_of_mem_lowerArc_and_endpointCut (right : Bool) {q : M}
    (hbottom : q ∈ B.lowerArc)
    (hcut : q ∈ (B.endpointEdge right).map '' Icc (0 : ℝ) 1) :
    q = (B.endpointEdge right).map 0 := by
  rw [B.lowerArc_eq_normalized_bottom] at hbottom
  obtain ⟨x, hx, hbottom⟩ := hbottom
  obtain ⟨t, ht, rfl⟩ := hcut
  have hsource {x z : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
      (hz : z ∈ Icc (0 : ℝ) (B.height x)) :
      collarParameterEquiv.symm (x, z) ∈ B.coordinates.source := by
    apply B.band_subset_source
    rw [B.band_eq_subgraph]
    simpa only [mem_ofPred_eq, collarParameterEquiv.apply_symm_apply, mem_Icc] using
      And.intro hx hz
  rw [B.endpointEdge_map] at hbottom
  let e : ℝ := if right then 1 else 0
  have he : e ∈ Icc (0 : ℝ) 1 := by cases right <;> simp [e]
  change B.coordinates (collarParameterEquiv.symm (x, 0)) =
    B.coordinates (collarParameterEquiv.symm (e, t * B.height e)) at hbottom
  have hpoint := B.coordinates.injOn
    (hsource hx ⟨le_rfl, (B.height_pos hx).le⟩)
    (hsource he
      ⟨mul_nonneg ht.1 (B.height_pos he).le,
        (mul_le_mul_of_nonneg_right ht.2 (B.height_pos he).le).trans_eq
          (one_mul _)⟩) hbottom
  have hz := congrArg (fun p => (collarParameterEquiv p).2) hpoint
  simp only [collarParameterEquiv.apply_symm_apply] at hz
  have ht0 : t = 0 := (mul_eq_zero.mp hz.symm).resolve_right
    (B.height_pos he).ne'
  rw [ht0]

end PoincareConjecture.Topology.Surface.ObliqueBandFaces
