import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.OriginalIncidentJoints
import PoincareConjecture.Proofs.M76.Dehn.OriginalDoubleArcTubeJointMaps

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.SignedJointCross

local notation "P2" => (ℝ × ℝ)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] (J : SignedJointCross E)


theorem exists_quarter_extension (b c : Bool)
    (e : ∀ j d, signedTubeRadius j d ≃ₜ J.radius j d)
    (he : ∀ j d, (e j d).IsFinitePL)
    (heCenter : ∀ j d (x : signedTubeRadius j d),
      (e j d x : E) = J.center ↔ (x : P2) = (0, 0))
    (heEnd : ∀ j d (x : signedTubeRadius j d),
      (e j d x : E) = J.endpoint j d ↔ (x : P2) = signedTubeCorner j d) :
    ∃ f : signedTubeQuarter b c ≃ₜ J.quarter b c, f.IsFinitePL ∧
      (∀ x : signedTubeRadius 0 c,
        (f ⟨x, (signedTube_quarter_ball b c).1 (Or.inr (Or.inl x.property))⟩ : E) = e 0 c x) ∧
      ∀ x : signedTubeRadius 1 b,
        (f ⟨x, (signedTube_quarter_ball b c).1 (Or.inr (Or.inr x.property))⟩ : E) = e 1 b x := by
  have hSource := signedTube_cross_radius_inter b c
  have hCross := J.cross_radii b c
  have hoverlap (x : signedTubeRadius 0 c) :
      (x : P2) ∈ signedTubeRadius 1 b ↔ (e 0 c x : E) ∈ J.radius 1 b := by
    have hs : (x : P2) ∈ signedTubeRadius 1 b ↔ (x : P2) = (0, 0) := by
      constructor
      · intro hx
        exact hSource.subset ⟨x.property, hx⟩
      · intro hx
        rw [hx]
        exact left_mem_segment ℝ _ _
    have ht : (e 0 c x : E) ∈ J.radius 1 b ↔ (e 0 c x : E) = J.center := by
      constructor
      · intro hx
        exact hCross.subset ⟨(e 0 c x).property, hx⟩
      · intro hx
        rw [hx]
        exact left_mem_segment ℝ _ _
    exact hs.trans ((heCenter 0 c x).symm.trans ht.symm)
  have hagree (x : P2) (hx : x ∈ signedTubeRadius 0 c) (hy : x ∈ signedTubeRadius 1 b) :
      (e 0 c ⟨x, hx⟩ : E) = e 1 b ⟨x, hy⟩ := by
    have hz : x = (0, 0) := hSource.subset ⟨hx, hy⟩
    exact ((heCenter 0 c ⟨x, hx⟩).mpr hz).trans ((heCenter 1 b ⟨x, hy⟩).mpr hz).symm
  obtain ⟨r, hr, hr0, hr1⟩ := Homeomorph.exists_union_finitePL
    (e 0 c) (e 1 b) (he 0 c) (he 1 b) hoverlap hagree
  have hEnd0 : signedTubeCorner 0 c ∈ signedTubeRadialRim b c :=
    Or.inl (right_mem_segment ℝ _ _)
  have hEnd1 : signedTubeCorner 1 b ∈ signedTubeRadialRim b c :=
    Or.inr (right_mem_segment ℝ _ _)
  have hrEnd0 : (r ⟨signedTubeCorner 0 c, hEnd0⟩ : E) = J.endpoint 0 c :=
    (hr0 ⟨signedTubeCorner 0 c, right_mem_segment ℝ _ _⟩).trans
      ((heEnd 0 c ⟨signedTubeCorner 0 c, right_mem_segment ℝ _ _⟩).mpr rfl)
  have hrEnd1 : (r ⟨signedTubeCorner 1 b, hEnd1⟩ : E) = J.endpoint 1 b :=
    (hr1 ⟨signedTubeCorner 1 b, right_mem_segment ℝ _ _⟩).trans
      ((heEnd 1 b ⟨signedTubeCorner 1 b, right_mem_segment ℝ _ _⟩).mpr rfl)
  have hrBoundary (x : signedTubeRadialRim b c) :
      (x : P2) ∈ ({signedTubeCorner 0 c, signedTubeCorner 1 b} : Set P2) ↔
        (r x : E) ∈ ({J.endpoint 0 c, J.endpoint 1 b} : Set E) := by
    have h0 : (r x : E) = J.endpoint 0 c ↔ (x : P2) = signedTubeCorner 0 c := by
      constructor
      · intro h
        exact congrArg Subtype.val (r.injective (Subtype.ext (h.trans hrEnd0.symm)))
      · intro h
        exact (congrArg (fun y : signedTubeRadialRim b c => (r y : E))
          (show x = ⟨signedTubeCorner 0 c, hEnd0⟩ from Subtype.ext h)).trans hrEnd0
    have h1 : (r x : E) = J.endpoint 1 b ↔ (x : P2) = signedTubeCorner 1 b := by
      constructor
      · intro h
        exact congrArg Subtype.val (r.injective (Subtype.ext (h.trans hrEnd1.symm)))
      · intro h
        exact (congrArg (fun y : signedTubeRadialRim b c => (r y : E))
          (show x = ⟨signedTubeCorner 1 b, hEnd1⟩ from Subtype.ext h)).trans hrEnd1
    simp only [mem_insert_iff, mem_singleton_iff, h0, h1]
  have hOuter : IsFinitePLBallPair ℝ (signedTubeOuterArc b c)
      {signedTubeCorner 0 c, signedTubeCorner 1 b} := by
    simpa only [signedTubeOuterArc, pair_comm] using signedTube_segment_ball
      (signedTubeCorner 1 b) (signedTubeCorner 0 c)
      (signedTube_corner_ne_corner 1 b 0 c (by simp))
  obtain ⟨f, hf, hfR, _, _⟩ := (signedTube_quarter_ball b c).exists_extension_of_boundary_piece
    (J.quarter_ball b c) hOuter (J.quarter_boundary_arcs b c).2.1
    (signedTube_outer_inter_rim b c)
    (by simpa only [inter_comm] using (J.quarter_boundary_arcs b c).2.2) r hr hrBoundary
  refine ⟨f, hf, ?_, ?_⟩
  · intro x
    exact (congrArg Subtype.val (hfR ⟨x, Or.inl x.property⟩)).trans (hr0 x)
  · intro x
    exact (congrArg Subtype.val (hfR ⟨x, Or.inr x.property⟩)).trans (hr1 x)



theorem exists_quarter_maps :
    ∃ (r : ∀ j b, signedTubeRadius j b ≃ₜ J.radius j b)
      (q : ∀ b c, signedTubeQuarter b c ≃ₜ J.quarter b c),
      (∀ j b, (r j b).IsFinitePL) ∧ (∀ b c, (q b c).IsFinitePL) ∧
      (∀ j b (x : signedTubeRadius j b), (r j b x : E) = J.center ↔ (x : P2) = (0, 0)) ∧
      (∀ j b (x : signedTubeRadius j b),
        (r j b x : E) = J.endpoint j b ↔ (x : P2) = signedTubeCorner j b) ∧
      (∀ b c (x : signedTubeRadius 0 c),
        (q b c ⟨x, (signedTube_quarter_ball b c).1 (Or.inr (Or.inl x.property))⟩ : E) = r 0 c x) ∧
      ∀ b c (x : signedTubeRadius 1 b),
        (q b c ⟨x, (signedTube_quarter_ball b c).1 (Or.inr (Or.inr x.property))⟩ : E) = r 1 b x := by
  choose r hr hc he using fun (j : Fin 2) (b : Bool) =>
    (signedTube_radius_ball j b).exists_marked_interval_homeomorph
      (J.radius_ball j b) (signedTube_corner_ne_center j b).symm (J.endpoint_ne_center j b).symm
  choose q hq hq0 hq1 using fun b c => J.exists_quarter_extension b c r hr hc he
  exact ⟨r, q, hr, hq, hc, he, hq0, hq1⟩

end PoincareConjecture.M76.Dehn.SignedJointCross
