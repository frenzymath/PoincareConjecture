import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Corners.VertexCaps









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff
open Poincare.Topology.Plane.Triangles

namespace PoincareConjecture.Topology.Surface

theorem mem_coordinateCap_iff
    {E : Type*} [TopologicalSpace E]
    (F : OpenPartialHomeomorph (ℝ × ℝ) E) (ε : ℝ)
    (hsource : {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ ε} ⊆ F.source)
    {z : E} (hz : z ∈ F.target) :
    z ∈ F '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ ε} ↔
      0 ≤ (F.symm z).1 ∧ 0 ≤ (F.symm z).2 ∧ (F.symm z).1 + (F.symm z).2 ≤ ε := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    simpa only [F.left_inv (hsource hq), mem_ofPred_eq] using hq
  · intro h
    exact ⟨F.symm z, h, F.right_inv hz⟩



theorem coordinateCap_eventually_mem_iff_active_constraints
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : OpenPartialHomeomorph (ℝ × ℝ) E) (ε : ℝ)
    (hsource : {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ ε} ⊆ F.source)
    {q : ℝ × ℝ} (hq₁ : 0 ≤ q.1) (hq₂ : 0 ≤ q.2) (hqs : q.1 + q.2 = ε) :
    ∀ᶠ z in 𝓝 (F q),
      z ∈ F '' {w : ℝ × ℝ | 0 ≤ w.1 ∧ 0 ≤ w.2 ∧ w.1 + w.2 ≤ ε} ↔
        (q.1 = 0 → 0 ≤ (F.symm z).1) ∧
        (q.2 = 0 → 0 ≤ (F.symm z).2) ∧ capExcess F ε z ≤ 0 := by
  have hq : q ∈ F.source := hsource ⟨hq₁, hq₂, hqs.le⟩
  have hc := F.continuousAt_symm (F.map_source hq)
  have hpos₁ : ∀ᶠ z in 𝓝 (F q), q.1 ≠ 0 → 0 < (F.symm z).1 := by
    by_cases h : q.1 = 0
    · exact Filter.Eventually.of_forall (fun _ hn => False.elim (hn h))
    · have hp : 0 < (F.symm (F q)).1 := by
        rw [F.left_inv hq]
        exact lt_of_le_of_ne hq₁ (Ne.symm h)
      exact (hc.fst.eventually (Ioi_mem_nhds hp)).mono (fun _ hz _ => hz)
  have hpos₂ : ∀ᶠ z in 𝓝 (F q), q.2 ≠ 0 → 0 < (F.symm z).2 := by
    by_cases h : q.2 = 0
    · exact Filter.Eventually.of_forall (fun _ hn => False.elim (hn h))
    · have hp : 0 < (F.symm (F q)).2 := by
        rw [F.left_inv hq]
        exact lt_of_le_of_ne hq₂ (Ne.symm h)
      exact (hc.snd.eventually (Ioi_mem_nhds hp)).mono (fun _ hz _ => hz)
  filter_upwards [F.open_target.mem_nhds (F.map_source hq), hpos₁, hpos₂] with z hz h₁ h₂
  rw [mem_coordinateCap_iff F ε hsource hz]
  unfold capExcess
  constructor
  · rintro ⟨ha, hb, hc⟩
    exact ⟨fun _ => ha, fun _ => hb, sub_nonpos.mpr hc⟩
  · rintro ⟨ha, hb, hc⟩
    refine ⟨?_, ?_, sub_nonpos.mp hc⟩
    · by_cases h : q.1 = 0
      · exact ha h
      · exact (h₁ h).le
    · by_cases h : q.2 = 0
      · exact hb h
      · exact (h₂ h).le



theorem coordinateCap_eventually_mem_iff_excess_nonpos
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : OpenPartialHomeomorph (ℝ × ℝ) E) (ε : ℝ)
    (hsource : {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ ε} ⊆ F.source)
    {q : ℝ × ℝ} (hq₁ : 0 < q.1) (hq₂ : 0 < q.2) (hqs : q.1 + q.2 = ε) :
    ∀ᶠ z in 𝓝 (F q),
      z ∈ F '' {w : ℝ × ℝ | 0 ≤ w.1 ∧ 0 ≤ w.2 ∧ w.1 + w.2 ≤ ε} ↔
        capExcess F ε z ≤ 0 := by
  simpa only [ne_of_gt hq₁, ne_of_gt hq₂, false_implies, true_and] using
    coordinateCap_eventually_mem_iff_active_constraints F ε hsource hq₁.le hq₂.le hqs

namespace ChartCircleArrangementVertexPatch.VertexCapFaces

variable {S : Type*} [TopologicalSpace S] [T2Space S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]
  {r : S → ℝ} {p : S} {P : ChartCircleArrangementVertexPatch r p}
  {x : Bool × Bool → S} (B : VertexCapFaces P x)

omit [T2Space S] in

theorem chart_carrier_eq_planar_cap (i : Bool × Bool) :
    chartAt (EuclideanSpace ℝ (Fin 2)) (x i) '' (B.face i).carrier =
      B.planarCoordinates i ''
        {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ B.scale} := by
  rw [B.carrier_planar]
  apply subset_antisymm
  · rintro z ⟨y, ⟨w, hw, rfl⟩, rfl⟩
    have ht : w ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) (x i)).target := by
      obtain ⟨q, hq, rfl⟩ := hw
      exact B.planar_target i ((B.planarCoordinates i).map_source (B.planar_source i hq))
    simpa only [(chartAt (EuclideanSpace ℝ (Fin 2)) (x i)).right_inv ht] using hw
  · rintro z ⟨q, hq, rfl⟩
    have ht := B.planar_target i ((B.planarCoordinates i).map_source (B.planar_source i hq))
    exact ⟨_, ⟨_, ⟨q, hq, rfl⟩, rfl⟩,
      (chartAt (EuclideanSpace ℝ (Fin 2)) (x i)).right_inv ht⟩

omit [T2Space S] in


theorem chart_carrier_first_tip_eventually_iff (i : Bool × Bool) :
    ∀ᶠ z in 𝓝 (chartAt (EuclideanSpace ℝ (Fin 2)) (x i)
      (P.sectorCoordinates i (B.scale, 0))),
      z ∈ chartAt (EuclideanSpace ℝ (Fin 2)) (x i) '' (B.face i).carrier ↔
        0 ≤ ((B.planarCoordinates i).symm z).2 ∧
          capExcess (B.planarCoordinates i) B.scale z ≤ 0 := by
  rw [B.chart_carrier_eq_planar_cap]
  have h := coordinateCap_eventually_mem_iff_active_constraints (B.planarCoordinates i)
    B.scale (B.planar_source i) (q := (B.scale, 0)) B.scale_pos.le le_rfl (add_zero _)
  rw [B.planar_first i B.scale ⟨B.scale_pos.le, le_rfl⟩] at h
  simpa only [Prod.fst, Prod.snd, B.scale_pos.ne', false_implies, true_implies, true_and] using h

omit [T2Space S] in

theorem chart_carrier_second_tip_eventually_iff (i : Bool × Bool) :
    ∀ᶠ z in 𝓝 (chartAt (EuclideanSpace ℝ (Fin 2)) (x i)
      (P.sectorCoordinates i (0, B.scale))),
      z ∈ chartAt (EuclideanSpace ℝ (Fin 2)) (x i) '' (B.face i).carrier ↔
        0 ≤ ((B.planarCoordinates i).symm z).1 ∧
          capExcess (B.planarCoordinates i) B.scale z ≤ 0 := by
  rw [B.chart_carrier_eq_planar_cap]
  have h := coordinateCap_eventually_mem_iff_active_constraints (B.planarCoordinates i)
    B.scale (B.planar_source i) (q := (0, B.scale)) le_rfl B.scale_pos.le (zero_add _)
  rw [B.planar_second i B.scale ⟨B.scale_pos.le, le_rfl⟩] at h
  simpa only [Prod.fst, Prod.snd, B.scale_pos.ne', false_implies, true_implies, true_and] using h

omit [T2Space S] in


theorem chart_carrier_chord_eventually_iff (i : Bool × Bool) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∀ᶠ z in 𝓝 ((1 - t) • B.planarCoordinates i (B.scale, 0) +
      t • B.planarCoordinates i (0, B.scale)),
      z ∈ chartAt (EuclideanSpace ℝ (Fin 2)) (x i) '' (B.face i).carrier ↔
        capExcess (B.planarCoordinates i) B.scale z ≤ 0 := by
  rw [B.chart_carrier_eq_planar_cap]
  have h := coordinateCap_eventually_mem_iff_excess_nonpos (B.planarCoordinates i)
    B.scale (B.planar_source i) (q := ((1 - t) * B.scale, t * B.scale))
    (mul_pos (sub_pos.mpr ht.2) B.scale_pos) (mul_pos ht.1 B.scale_pos) (by ring)
  simpa only [B.planar_chord] using h

end ChartCircleArrangementVertexPatch.VertexCapFaces

end PoincareConjecture.Topology.Surface
