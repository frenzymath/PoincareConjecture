import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Collar.Mesh.ChartMotion
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Whole.PairChart

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76
local notation "E" => ((ℝ × ℝ) × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem OriginalSurfacePairChart.exists_target_preserving_point_motion
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {S T : Set X} {y : X} {b : Bool}
    (C : OriginalSurfacePairChart e S T y b)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {U : Set X} (hU : IsOpen U) (hyU : y ∈ U) :
    ∃ (F : X ≃ₜ X) (K : Set X),
      IsCompact K ∧ K ⊆ U ∧ EqOn F id Kᶜ ∧
      (∀ i j, (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (F.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      F ⁻¹' T = T ∧ y ∉ F '' S ∧
      ∀ (R : Set X) (A : Set (ℝ × ℝ)),
        (∀ z ∈ C.coordinates.source,
          C.chart.symm z ∈ R ↔ (C.coordinates z).1 ∈ A) → F ⁻¹' R = R := by
  let Q := (C.chart.trans C.coordinates).symm
  have hyQ : y ∈ Q.target := ⟨C.center_source, C.center_coordinates⟩
  have hQy : Q.symm y = 0 := C.center_zero
  have hzeroQ : (0 : E) ∈ Q.source := hQy ▸ Q.map_target hyQ
  have hQzero : Q 0 = y := by rw [← hQy, Q.right_inv hyQ]
  let O : Set E := Q.source ∩ Q ⁻¹' U
  have hO : IsOpen O := Q.isOpen_inter_preimage hU
  have hzeroO : (0 : E) ∈ O := ⟨hzeroQ, by change Q 0 ∈ U; rw [hQzero]; exact hyU⟩
  obtain ⟨ε, hε, hεO⟩ := Metric.isOpen_iff.mp hO 0 hzeroO
  let r := ε / 2
  have hr : 0 < r := half_pos hε
  have hballO : closedBall (0 : E) r ⊆ O := by
    intro z hz
    apply hεO
    exact (mem_closedBall.mp hz).trans_lt (half_lt_self hε)
  have hballQ := hballO.trans inter_subset_left
  obtain ⟨H, hHPL, hHoff, hfirst, _, havoid⟩ :=
    CollarMesh.exists_normal_motion_avoiding_plane (r := r)
      (c := (1 : ℝ) / 2) (by norm_num) (by norm_num)
  obtain ⟨F, hFQ, hFoff⟩ :=
    Q.exists_supported_chart_homeomorph H (isCompact_closedBall _ _) hballQ hHoff
  have hforward (i j : ι) : (e i).symm.trans
      (F.toOpenPartialHomeomorph.trans (e j)) ∈ piecewiseAffineGroupoid V3 := by
    apply CollarMesh.supported_chart_transition_PL Q (e i).symm (e j).symm H F
      (isCompact_closedBall _ _) hballQ hHoff hFQ hFoff hHPL
    · have h := ((mem_piecewiseAffineGroupoid_iff V3 _).mp (C.compatible i)).1
      simpa only [Q, OpenPartialHomeomorph.symm_symm, OpenPartialHomeomorph.coe_trans,
        OpenPartialHomeomorph.trans_source, preimage_inter, preimage_comp, inter_assoc,
        Function.comp_assoc] using C.forwardPL.comp h
    · have h := ((mem_piecewiseAffineGroupoid_iff V3 _).mp
        ((piecewiseAffineGroupoid V3).symm (C.compatible j))).1
      simpa only [Q, OpenPartialHomeomorph.symm_symm,
        OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.coe_trans,
        OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
        preimage_inter, preimage_comp, inter_assoc,
        Function.comp_assoc] using h.comp C.inversePL
    · exact he i j
  have hpreserve (R : Set X) (A : Set (ℝ × ℝ))
      (hR : ∀ z ∈ C.coordinates.source,
        C.chart.symm z ∈ R ↔ (C.coordinates z).1 ∈ A) : F ⁻¹' R = R := by
    apply Q.supported_chart_preimage_region H F hballQ hHoff hFQ hFoff
      (B := {p : E | p.1 ∈ A})
    · intro p hp
      have hpc : p ∈ C.coordinates.target := hp.1
      have hsrc := C.coordinates.map_target hpc
      change C.chart.symm (C.coordinates.symm p) ∈ R ↔ p.1 ∈ A
      simpa only [C.coordinates.right_inv hpc] using hR _ hsrc
    · intro p
      change (H p).1 ∈ A ↔ p.1 ∈ A
      rw [hfirst]
  refine ⟨F, Q '' closedBall (0 : E) r,
    (isCompact_closedBall _ _).image_of_continuousOn (Q.continuousOn.mono hballQ),
    ?_, hFoff, hforward, ?_, ?_, ?_, hpreserve⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact (hballO hz).2
  · intro i j
    simpa only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm, OpenPartialHomeomorph.trans_assoc,
      Homeomorph.symm_toOpenPartialHomeomorph] using
      (piecewiseAffineGroupoid V3).symm (hforward j i)
  · exact hpreserve T {p : ℝ × ℝ | p.1 = 0 ∧ (b = true → 0 ≤ p.2)}
      C.second_surface
  · rintro ⟨x, hxS, hxy⟩
    have hxQ : x ∈ Q.target := by
      by_contra hn
      have hxK : x ∉ Q '' closedBall (0 : E) r := by
        rintro ⟨z, hz, rfl⟩
        exact hn (Q.map_source (hballQ hz))
      have hxeq : x = y := (hFoff hxK).symm.trans hxy
      exact hn (hxeq.symm ▸ hyQ)
    have hxfirst : (Q.symm x).2 = 0 := by
      have hsrc : C.chart x ∈ C.coordinates.source := hxQ.2
      have hs := (C.first_surface _ hsrc).mp
        (by simpa only [C.chart.left_inv hxQ.1] using hxS)
      exact hs.1
    have hHxQ : H (Q.symm x) ∈ Q.source := by
      by_contra hn
      have hout : H (Q.symm x) ∉ closedBall (0 : E) r := fun h => hn (hballQ h)
      have heq : H (Q.symm x) = Q.symm x := H.injective (hHoff hout)
      exact hn (heq.symm ▸ Q.map_target hxQ)
    have hHzero : H (Q.symm x) = 0 := by
      apply Q.injOn hHxQ hzeroQ
      exact (hFQ hxQ).symm.trans (hxy.trans hQzero.symm)
    exact disjoint_left.mp havoid ⟨Q.symm x, hxfirst, hHzero⟩
      ⟨rfl, mem_ball_self hr⟩

end PoincareConjecture.M76
