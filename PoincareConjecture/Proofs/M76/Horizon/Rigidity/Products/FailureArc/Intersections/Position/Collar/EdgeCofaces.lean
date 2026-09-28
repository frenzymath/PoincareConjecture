import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Collar.EdgeCoordinates
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.LeafFields.OriginalEdgeCofaceCharts

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

theorem finite_contacts_and_coface_charts_of_affine_surface
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
    [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (K : SimplicialComplex ℝ E) {g : E → X}
    {p q : E} (hpq : ({p, q} : Finset E) ∈ K.faces)
    (B : OpenPartialHomeomorph X V3)
    (hB : ∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3)
    (A : V3 →ᴬ[ℝ] ℝ)
    (hS : ∀ z ∈ B.target, B.symm z ∈ S ↔ A z = 0)
    (hp : A (B (g p)) < 0) (hq : 0 < A (B (g q)))
    (hcofaces : ∀ t ∈ K.faces, ({p, q} : Finset E) ⊆ t →
      MapsTo g (convexHull ℝ (t : Set E)) B.source ∧
      ∃ D : E →ᴬ[ℝ] V3, EqOn (B ∘ g) D (convexHull ℝ (t : Set E))) :
    (S ∩ (g '' convexHull ℝ ({p, q} : Set E))).Finite ∧
      HasOriginalEdgeCofaceCharts e S K g {p, q} := by
  obtain ⟨hmap, D, hD⟩ := hcofaces {p, q} hpq (Subset.refl _)
  have hmapseg : MapsTo g (segment ℝ p q) B.source := by
    simpa only [Finset.coe_pair, convexHull_pair] using hmap
  have hDseg : EqOn (B ∘ g) D (segment ℝ p q) := by
    simpa only [Finset.coe_pair, convexHull_pair] using hD
  have hDp : D p = B (g p) := (hDseg (left_mem_segment ℝ p q)).symm
  have hDq : D q = B (g q) := (hDseg (right_mem_segment ℝ p q)).symm
  have himage : (B ∘ g) '' segment ℝ p q = segment ℝ (B (g p)) (B (g q)) := by
    rw [image_congr hDseg]
    have hh : D '' segment ℝ p q = segment ℝ (D p) (D q) :=
      image_segment ℝ D.toAffineMap p q
    simpa only [hDp, hDq] using hh
  have hphysical (z : V3) (hz : z ∈ B.target) :
      B.symm z ∈ g '' segment ℝ p q ↔ z ∈ segment ℝ (B (g p)) (B (g q)) := by
    rw [← himage]
    constructor
    · rintro ⟨x, hx, hxy⟩
      exact ⟨x, hx, (congrArg B hxy).trans (B.right_inv hz)⟩
    · rintro ⟨x, hx, hxy⟩
      exact ⟨x, hx, (B.left_inv (hmapseg hx)).symm.trans (congrArg B.symm hxy)⟩
  have hcharts (y : X) (hy : y ∈ S ∩ (g '' segment ℝ p q)) :
      ∃ (F : C3 ≃ᴬ[ℝ] V3) (V : Set V3),
        y ∈ B.source ∧ IsOpen V ∧ B y ∈ V ∧ V ⊆ B.target ∧ F 0 = B y ∧
        (∀ z, A (F z) = z.2) ∧
        ∀ z, F z ∈ V → (F z ∈ segment ℝ (B (g p)) (B (g q)) ↔ z.1 = 0) := by
    obtain ⟨x, hx, hxy⟩ := hy.2
    have hyB : y ∈ B.source := hxy ▸ hmapseg hx
    have hyseg : B y ∈ segment ℝ (B (g p)) (B (g q)) := by
      apply (hphysical _ (B.map_source hyB)).mp
      simpa only [B.left_inv hyB] using hy.2
    have hyzero : A (B y) = 0 := (hS _ (B.map_source hyB)).mp
      (by simpa only [B.left_inv hyB] using hy.1)
    obtain ⟨F, V, hV, hyV, hVB, hF, hheight, hedge⟩ :=
      exists_affine_plane_edge_crossing (by simp) A hp hq hyseg hyzero
        B.open_target (B.map_source hyB)
    exact ⟨F, V, hyB, hV, hyV, hVB, hF, hheight, hedge⟩
  have hfinite : (S ∩ (g '' segment ℝ p q)).Finite := by
    apply Set.Subsingleton.finite
    intro y hy z hz
    obtain ⟨F, V, hyB, _, _, hVB, hF, hheight, _⟩ := hcharts y hy
    obtain ⟨x, hx, hxz⟩ := hz.2
    have hzB : z ∈ B.source := hxz ▸ hmapseg hx
    have hzseg : B z ∈ segment ℝ (B (g p)) (B (g q)) := by
      apply (hphysical _ (B.map_source hzB)).mp
      simpa only [B.left_inv hzB] using hz.2
    have hzheight : A (B z) = 0 := (hS _ (B.map_source hzB)).mp
      (by simpa only [B.left_inv hzB] using hz.1)
    have hyheight : A (B y) = 0 := by rw [← hF, hheight]; rfl
    obtain ⟨ty, _, hty⟩ := (segment_eq_image_lineMap ℝ _ _).subset
      ((hphysical _ (B.map_source hyB)).mp (by simpa only [B.left_inv hyB] using hy.2))
    obtain ⟨tz, _, htz⟩ := (segment_eq_image_lineMap ℝ _ _).subset hzseg
    have hyval := congrArg A.toAffineMap hty
    have hzval := congrArg A.toAffineMap htz
    rw [A.toAffineMap.apply_lineMap] at hyval hzval
    change AffineMap.lineMap (A (B (g p))) (A (B (g q))) ty = A (B y) at hyval
    change AffineMap.lineMap (A (B (g p))) (A (B (g q))) tz = A (B z) at hzval
    simp only [AffineMap.lineMap_apply_module, smul_eq_mul] at hyval hzval
    have htyz : ty = tz := by
      have hgap : A (B (g q)) - A (B (g p)) ≠ 0 := (sub_pos.mpr (hp.trans hq)).ne'
      have heq : (ty - tz) * (A (B (g q)) - A (B (g p))) = 0 := by
        rw [hyheight] at hyval
        rw [hzheight] at hzval
        nlinarith
      exact sub_eq_zero.mp ((mul_eq_zero.mp heq).resolve_right hgap)
    exact B.injOn hyB hzB (hty.symm.trans (htyz ▸ htz))
  refine ⟨by simpa only [convexHull_pair] using hfinite, ?_⟩
  intro y hy
  simp only [Finset.coe_pair, convexHull_pair] at hy
  obtain ⟨F, V, hyB, hV, hyV, hVB, hF, hheight, hedge⟩ := hcharts y hy
  refine ⟨B, V, F, hB, hyB, hV, hyV, hVB, hF, ?_, ?_, hcofaces⟩
  · intro z hz
    rw [hS _ (hVB hz), hheight]
  · intro z hz
    simpa only [Finset.coe_pair, convexHull_pair] using
      (hphysical _ (hVB hz)).trans (hedge z hz)

end PoincareConjecture.M76
