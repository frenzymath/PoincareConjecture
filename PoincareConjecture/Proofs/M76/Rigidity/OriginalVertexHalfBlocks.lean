import PoincareConjecture.Proofs.M76.Rigidity.OriginalVertexHalfCharts









set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.OriginalProperDiskTriangulation

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
  (T : OriginalProperDiskTriangulation e R j)

open Classical in



theorem vertex_half_ball_pairs (p : (T.marked 2).vertices) (w : ℝ) (hw : w ≠ 0) :
    let N := T.vertexBlock p
    let Z : Set (T.index → ℝ × V3) :=
      {x | 0 ≤ w * (T.chart (T.chart_index p) (T.inverse x)).2}
    let O := ((N.link p).space ∩ (T.marked 0).space) ∩ Z
    let C := ((N.space ∩ (T.marked 1).space) ∩ Z) ∪ (N.space ∩ (T.marked 2).space)
    IsFinitePLBallPair C3 ((N.space ∩ (T.marked 0).space) ∩ Z) (O ∪ C) ∧
      IsFinitePLBallPair (ℝ × ℝ) O (O ∩ C) ∧ (O \ C).Nonempty := by
  classical
  let N := T.vertexBlock p
  let Z : Set (T.index → ℝ × V3) :=
    {x | 0 ≤ w * (T.chart (T.chart_index p) (T.inverse x)).2}
  let O := ((N.link p).space ∩ (T.marked 0).space) ∩ Z
  let C := ((N.space ∩ (T.marked 1).space) ∩ Z) ∪ (N.space ∩ (T.marked 2).space)
  change IsFinitePLBallPair C3 ((N.space ∩ (T.marked 0).space) ∩ Z) (O ∪ C) ∧
    IsFinitePLBallPair (ℝ × ℝ) O (O ∩ C) ∧ (O \ C).Nonempty
  obtain ⟨hN, hpN, hstar, _, _⟩ := T.vertexBlock_centered_chart p
  obtain ⟨boundary, g, hg, hgi, hgp, hgint, hnormal, hregion, hdisk, hfront⟩ :=
    T.exists_vertex_half_chart p w hw
  let c : C3 ≃L[ℝ] (Fin 3 → ℝ) := ContinuousLinearEquiv.ofFinrankEq
    (by simp [Module.finrank_prod])
  obtain ⟨hhalf, hcap⟩ :=
    hg.conical_halfBlock_ball_pairs hN hgi hpN hstar hgp hgint c boundary
  have hlinksub : (N.link p).space ⊆ N.space :=
    SimplicialComplex.space_subset_of_le (show N.link p ≤ N from fun _ hs => hs.1)
  have hbody : SimplicialComplex.chartedHalfBlock N.space g boundary =
      (N.space ∩ (T.marked 0).space) ∩ Z := by
    ext x
    change (x ∈ N.space ∧ (boundary = true → 0 ≤ (g x).1.1) ∧ 0 ≤ (g x).2) ↔
      ((x ∈ N.space ∧ x ∈ (T.marked 0).space) ∧
        0 ≤ w * (T.chart (T.chart_index p) (T.inverse x)).2)
    by_cases hxN : x ∈ N.space
    · rw [← hregion x hxN, hnormal]
      tauto
    · tauto
  have hout : SimplicialComplex.chartedHalfBlockOuter (N.link p).space g boundary = O := by
    ext x
    change (x ∈ (N.link p).space ∧
        (boundary = true → 0 ≤ (g x).1.1) ∧ 0 ≤ (g x).2) ↔
      ((x ∈ (N.link p).space ∧ x ∈ (T.marked 0).space) ∧
        0 ≤ w * (T.chart (T.chart_index p) (T.inverse x)).2)
    by_cases hxL : x ∈ (N.link p).space
    · rw [← hregion x (hlinksub hxL), hnormal]
      tauto
    · tauto
  have hactive : SimplicialComplex.chartedHalfBlockActive N.space g boundary = C := by
    ext x
    constructor
    · rintro ⟨hxN, hr, hn, hF | hD⟩
      · have hn' : x ∈ Z := by
          change 0 ≤ w * (T.chart (T.chart_index p) (T.inverse x)).2
          rwa [hnormal x] at hn
        exact Or.inl ⟨⟨hxN, (hfront x hxN).mpr hF⟩, hn'⟩
      · exact Or.inr ⟨hxN, (hdisk x hxN).mpr ⟨hr, hD⟩⟩
    · rintro (⟨⟨hxN, hxF⟩, hn⟩ | ⟨hxN, hxD⟩)
      · have hxG := (hfront x hxN).mp hxF
        refine ⟨hxN, ?_, (hnormal x).symm ▸ hn, Or.inl hxG⟩
        intro _
        exact hxG.2.ge
      · obtain ⟨hr, hz⟩ := (hdisk x hxN).mp hxD
        exact ⟨hxN, hr, hz.ge, Or.inr hz⟩
  rw [hbody, hout, hactive] at hhalf
  rw [hout, hactive] at hcap
  obtain ⟨x, hx, hnot⟩ := hcap.sdiff_nonempty
  exact ⟨hhalf, hcap, x, hx, fun hC => hnot ⟨hx, hC⟩⟩

end PoincareConjecture.M76.OriginalProperDiskTriangulation
