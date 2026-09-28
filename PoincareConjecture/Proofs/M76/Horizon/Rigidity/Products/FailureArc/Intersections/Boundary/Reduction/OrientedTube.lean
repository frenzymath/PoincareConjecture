import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Reduction.LongitudinalTube
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Spanning.EndpointOrder
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Spanning.Canonical
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Tubes.Strips.RimEnds



set_option autoImplicit false
open Set Geometry Topology PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.Annuli
open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Ann" => squareAnnulus 8 1
local notation "Src" => PolygonalCrossingResolution.source
local notation "Last" => Set.ofPred (fun x : P2 => depth 8 x = 1)

theorem OriginalIntervalTube.exists_oriented_whole
    {X ι : Type*} [MetricSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R W : Set X} (F : Bool → Set X)
    {f g : P2 → X}
    (U : OriginalIntervalTube e R W Ann Ann
      (Ann ∩ g ⁻¹' (f '' Ann)) (Ann ∩ f ⁻¹' (g '' Ann)) g f)
    (hF : ∀ b, F b ⊆ frontier R) (hdis : Disjoint (F false) (F true))
    (hfp : ∀ x ∈ Ann, f x ∈ frontier R ↔ x ∈ frontier Ann)
    (hgp : ∀ x ∈ Ann, g x ∈ frontier R ↔ x ∈ frontier Ann)
    (hfmark : ∀ x ∈ Ann, f x ∈ F false ↔ depth 8 x = -1)
    (hgmark : ∀ x ∈ Ann, g x ∈ F false ↔ depth 8 x = -1)
    (hglast : MapsTo g (Ann ∩ Last) (F true))
    (p : X) (hpoint : ((f '' Ann) ∩ (g '' Ann)) ∩ F false = {p})
    (hlast : (((f '' Ann) ∩ (g '' Ann)) ∩ F true).Nonempty) :
    ∃ V : OriginalIntervalTube e R W Ann Ann
        (Ann ∩ g ⁻¹' (f '' Ann)) (Ann ∩ f ⁻¹' (g '' Ann)) g f,
      V.map ((0, 0), 0) = p ∧ V.map ((0, 0), 1) ∈ F true ∧
      (∀ t ∈ Icc (0 : ℝ) 1, V.map ((0, 0), t) ∈ F false ↔ t = 0) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, V.map ((0, 0), t) ∈ F true ↔ t = 1) ∧
      (∀ q ∈ Src, depth 8 (V.first q) = -1 ↔ q.1 = 0) ∧
      (∀ q ∈ Src, depth 8 (V.first q) = 1 ↔ q.1 = 1) ∧
      (∀ q ∈ Src, depth 8 (V.second q) = -1 ↔ q.1 = 0) ∧
      (∀ q ∈ Src, depth 8 (V.second q) = 1 ↔ q.1 = 1) := by
  have hzero : (0, 0) ∈ Src := by norm_num [PolygonalCrossingResolution.source]
  have hone : (1, 0) ∈ Src := by norm_num [PolygonalCrossingResolution.source]
  have axis (V : OriginalIntervalTube e R W Ann Ann
      (Ann ∩ g ⁻¹' (f '' Ann)) (Ann ∩ f ⁻¹' (g '' Ann)) g f)
      (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      g (V.first (t, 0)) = V.map ((0, 0), t) ∧
      f (V.second (t, 0)) = V.map ((0, 0), t) := by
    constructor
    · simpa [originalStripSheet] using V.first_sheet (t, 0) ⟨ht, by norm_num⟩
    · simpa [originalStripSheet] using V.second_sheet (t, 0) ⟨ht, by norm_num⟩
  have hu (x : P2) (hx : x ∈ Ann) : g x ∈ F false ∪ F true ↔ g x ∈ frontier R := by
    constructor
    · rintro (h | h)
      · exact hF false h
      · exact hF true h
    · intro h
      rcases (mem_frontier_planar_annulus_iff x).mp ((hgp x hx).mp h) with h | h
      · exact Or.inl ((hgmark x hx).mpr h)
      · exact Or.inr (hglast ⟨hx, h⟩)
  have hfront (q : P2) (hq : q ∈ Src) :
      (g ∘ U.first) q ∈ F false ∪ F true ↔ q.1 = 0 ∨ q.1 = 1 := by
    change g (U.first q) ∈ F false ∪ F true ↔ _
    rw [hu _ (U.first_mapsTo hq), U.first_sheet q hq]
    exact U.frontier_iff _ (originalStripSheet_mem_tube false hq)
  have himage : (g ∘ U.first) '' arm 0 = f '' Ann ∩ g '' Ann := by
    rw [image_comp, U.first_center]
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hx.2, x, hx.1, rfl⟩
    · rintro ⟨hz, x, hx, rfl⟩
      exact ⟨x, ⟨hx, hz⟩, rfl⟩
  have hfirst : (((g ∘ U.first) '' arm 0) ∩ F false).Nonempty := by
    rw [himage, hpoint]
    exact singleton_nonempty p
  have hlast' : (((g ∘ U.first) '' arm 0) ∩ F true).Nonempty := himage.symm ▸ hlast
  obtain ⟨V, hv0, hv1⟩ : ∃ V : OriginalIntervalTube e R W Ann Ann
      (Ann ∩ g ⁻¹' (f '' Ann)) (Ann ∩ f ⁻¹' (g '' Ann)) g f,
      g (V.first (0, 0)) ∈ F false ∧ g (V.first (1, 0)) ∈ F true := by
    rcases spanning_center_endpoint_order (g ∘ U.first) hdis hfront hfirst hlast' with h | h
    · exact ⟨U, h⟩
    · refine ⟨U.longitudinalReverse, ?_, ?_⟩
      · simpa [OriginalIntervalTube.longitudinalReverse, spanningSourceReverse_apply] using h.2
      · simpa [OriginalIntervalTube.longitudinalReverse, spanningSourceReverse_apply] using h.1
  have hQdis : Disjoint (frontier spanningOuterSquare) (frontier spanningInnerSquare) := by
    apply disjoint_left.mpr
    intro x hx hy
    have hx' := (spanning_outer_frontier x).mp hx
    have hy' := (spanning_inner_frontier x).mp hy
    linarith
  have hs {c : P2 → P2} {a : P2 → X} (hc : ContinuousOn c Src) (hcS : MapsTo c Src Ann)
      (hap : ∀ x ∈ Ann, a x ∈ frontier R ↔ x ∈ frontier Ann)
      (ham : ∀ x ∈ Ann, a x ∈ F false ↔ depth 8 x = -1)
      (hcf : ∀ q ∈ Src, a (c q) ∈ frontier R ↔ q.1 = 0 ∨ q.1 = 1)
      (hc0 : a (c (0, 0)) ∈ F false) (hc1 : a (c (1, 0)) ∈ F true) :
      (∀ q ∈ Src, depth 8 (c q) = -1 ↔ q.1 = 0) ∧
      (∀ q ∈ Src, depth 8 (c q) = 1 ↔ q.1 = 1) := by
    have hcf' (q : P2) (hq : q ∈ Src) :
        c q ∈ frontier spanningOuterSquare ∪ frontier spanningInnerSquare ↔ q.1 = 0 ∨ q.1 = 1 := by
      rw [mem_union, spanning_outer_frontier, spanning_inner_frontier,
        ← mem_frontier_planar_annulus_iff, ← hap _ (hcS hq)]
      exact hcf q hq
    have h0 : c (0, 0) ∈ frontier spanningOuterSquare :=
      (spanning_outer_frontier _).mpr ((ham _ (hcS hzero)).mp hc0)
    have h1 : c (1, 0) ∈ frontier spanningInnerSquare := by
      have hh := (mem_frontier_planar_annulus_iff _).mp ((hap _ (hcS hone)).mp (hF true hc1))
      apply (spanning_inner_frontier _).mpr
      exact hh.resolve_left (fun hh ↦ disjoint_left.mp hdis ((ham _ (hcS hone)).mpr hh) hc1)
    have hh := proper_strip_separate_rims hc isClosed_frontier isClosed_frontier hQdis hcf' h0 h1
    simpa only [spanning_outer_frontier, spanning_inner_frontier] using hh
  have hfirstFront (q : P2) (hq : q ∈ Src) : g (V.first q) ∈ frontier R ↔ q.1 = 0 ∨ q.1 = 1 := by
    rw [V.first_sheet q hq]
    exact V.frontier_iff _ (originalStripSheet_mem_tube false hq)
  have hsecondFront (q : P2) (hq : q ∈ Src) : f (V.second q) ∈ frontier R ↔ q.1 = 0 ∨ q.1 = 1 := by
    rw [V.second_sheet q hq]
    exact V.frontier_iff _ (originalStripSheet_mem_tube true hq)
  have hs0 := hs V.first_pl.continuousOn V.first_mapsTo hgp hgmark hfirstFront hv0 hv1
  have hs1 := hs V.second_pl.continuousOn V.second_mapsTo hfp hfmark hsecondFront
    ((axis V 0 (by norm_num)).2.trans (axis V 0 (by norm_num)).1.symm ▸ hv0)
    ((axis V 1 (by norm_num)).2.trans (axis V 1 (by norm_num)).1.symm ▸ hv1)
  have hp0 : V.map ((0, 0), 0) = p := by
    have hc : V.first (0, 0) ∈ Ann ∩ g ⁻¹' (f '' Ann) :=
      V.first_center.subset ⟨(0, 0), by norm_num [arm], rfl⟩
    have hh : g (V.first (0, 0)) = p := mem_singleton_iff.mp
      (hpoint.subset ⟨⟨hc.2, V.first (0, 0), hc.1, rfl⟩, hv0⟩)
    exact (axis V 0 (by norm_num)).1.symm.trans hh
  refine ⟨V, hp0, (axis V 1 (by norm_num)).1 ▸ hv1, ?_, ?_, hs0.1, hs0.2, hs1.1, hs1.2⟩
  · intro t ht
    rw [← (axis V t ht).1, hgmark _ (V.first_mapsTo ⟨ht, by norm_num⟩)]
    exact hs0.1 (t, 0) ⟨ht, by norm_num⟩
  · intro t ht
    rw [← (axis V t ht).1]
    constructor
    · intro hh
      have hh' := (hfirstFront (t, 0) ⟨ht, by norm_num⟩).mp (hF true hh)
      exact hh'.resolve_left (fun hbad ↦ disjoint_left.mp hdis
        ((hgmark _ (V.first_mapsTo ⟨ht, by norm_num⟩)).mpr
          ((hs0.1 (t, 0) ⟨ht, by norm_num⟩).mpr hbad)) hh)
    · rintro rfl
      exact hv1

end PoincareConjecture.M76.Dehn.Annuli
