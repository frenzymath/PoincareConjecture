import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Collar.Mesh.PointMotion
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Collar.Mesh.GraphCoordinates

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76
local notation "E" => ((ℝ × ℝ) × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem OriginalSurfacePairChart.exists_supported_normal_motion
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {S T : Set X} {y : X} {b : Bool}
    (C : OriginalSurfacePairChart e S T y b)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {r c : ℝ} (H : E ≃ₜ E)
    (hHPL : H.toOpenPartialHomeomorph ∈ piecewiseAffineGroupoid E)
    (hval : ∀ p, H p = (p.1, p.2 + c * CollarMesh.normalMargin r p))
    (hHoff : EqOn H id (closedBall (0 : E) r)ᶜ)
    (hball : closedBall (0 : E) r ⊆ (C.chart.trans C.coordinates).target) :
    ∃ F : X ≃ₜ X,
      EqOn F ((C.chart.trans C.coordinates).trans
        (H.toOpenPartialHomeomorph.trans (C.chart.trans C.coordinates).symm))
        (C.chart.trans C.coordinates).source ∧
      EqOn F id ((C.chart.trans C.coordinates).symm '' closedBall (0 : E) r)ᶜ ∧
      (∀ i j, (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (F.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      F ⁻¹' T = T ∧
      (∀ z ∈ (C.chart.trans C.coordinates).target,
        (C.chart.trans C.coordinates).symm z ∈ F '' S ↔
          (CollarMesh.normalGraphCoordinates r c z).2 = 0 ∧
            (b = true → 0 ≤ z.1.2)) ∧
      ∀ (R : Set X) (A : Set (ℝ × ℝ)),
        (∀ z ∈ C.coordinates.source,
          C.chart.symm z ∈ R ↔ (C.coordinates z).1 ∈ A) → F ⁻¹' R = R := by
  let Q := (C.chart.trans C.coordinates).symm
  have hfirst (p : E) : (H p).1 = p.1 := by rw [hval]
  obtain ⟨F, hFQ, hFoff⟩ :=
    Q.exists_supported_chart_homeomorph H (isCompact_closedBall _ _) hball hHoff
  have hforward (i j : ι) : (e i).symm.trans
      (F.toOpenPartialHomeomorph.trans (e j)) ∈ piecewiseAffineGroupoid V3 := by
    apply CollarMesh.supported_chart_transition_PL Q (e i).symm (e j).symm H F
      (isCompact_closedBall _ _) hball hHoff hFQ hFoff hHPL
    · have h := ((mem_piecewiseAffineGroupoid_iff V3 _).mp (C.compatible i)).1
      simpa only [Q, OpenPartialHomeomorph.symm_symm, OpenPartialHomeomorph.coe_trans,
        OpenPartialHomeomorph.trans_source, preimage_inter, preimage_comp, inter_assoc,
        Function.comp_assoc] using C.forwardPL.comp h
    · have h := ((mem_piecewiseAffineGroupoid_iff V3 _).mp
        ((piecewiseAffineGroupoid V3).symm (C.compatible j))).1
      simpa only [Q, OpenPartialHomeomorph.symm_symm,
        OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.coe_trans,
        OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
        preimage_inter, preimage_comp, inter_assoc, Function.comp_assoc] using h.comp C.inversePL
    · exact he i j
  have hpreserve (R : Set X) (A : Set (ℝ × ℝ))
      (hR : ∀ z ∈ C.coordinates.source,
        C.chart.symm z ∈ R ↔ (C.coordinates z).1 ∈ A) : F ⁻¹' R = R := by
    apply Q.supported_chart_preimage_region H F hball hHoff hFQ hFoff
      (B := {p : E | p.1 ∈ A})
    · intro p hp
      have hpc : p ∈ C.coordinates.target := hp.1
      change C.chart.symm (C.coordinates.symm p) ∈ R ↔ p.1 ∈ A
      simpa only [C.coordinates.right_inv hpc] using
        hR _ (C.coordinates.map_target hpc)
    · intro p
      change (H p).1 ∈ A ↔ p.1 ∈ A
      rw [hfirst]
  refine ⟨F, hFQ, hFoff, hforward, ?_, ?_, ?_, hpreserve⟩
  · intro i j
    simpa only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm, OpenPartialHomeomorph.trans_assoc,
      Homeomorph.symm_toOpenPartialHomeomorph] using
      (piecewiseAffineGroupoid V3).symm (hforward j i)
  · exact hpreserve T {p : ℝ × ℝ | p.1 = 0 ∧ (b = true → 0 ≤ p.2)} C.second_surface
  · let P : Set E := {p | p.2 = 0 ∧ (b = true → 0 ≤ p.1.2)}
    have hmodel : ∀ p ∈ Q.source, Q p ∈ S ↔ p ∈ P := by
      intro p hp
      have hpc : p ∈ C.coordinates.target := hp.1
      change C.chart.symm (C.coordinates.symm p) ∈ S ↔
        p.2 = 0 ∧ (b = true → 0 ≤ p.1.2)
      simpa only [C.coordinates.right_inv hpc] using
        C.first_surface _ (C.coordinates.map_target hpc)
    intro z hz
    rw [CollarMesh.supported_chart_moved_set Q H F hball hHoff hFQ hmodel z hz]
    rw [← CollarMesh.normalGraphCoordinates_surface hval]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨⟨w, hw.1, rfl⟩, by simpa only [hfirst] using hw.2⟩
    · rintro ⟨⟨w, hw, rfl⟩, hinward⟩
      exact ⟨w, ⟨hw, by simpa only [hfirst] using hinward⟩, rfl⟩

end PoincareConjecture.M76
