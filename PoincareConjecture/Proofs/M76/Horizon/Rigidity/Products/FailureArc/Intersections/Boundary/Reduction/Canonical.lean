import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Reduction.Step
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Reparametrization.Reflection

set_option autoImplicit false
open Set Geometry Topology PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Ann" => squareAnnulus 8 1
local notation "First" => Set.ofPred (fun x : P2 => depth 8 x = -1)
local notation "Last" => Set.ofPred (fun x : P2 => depth 8 x = 1)

theorem canonical_returning_reduction_or_components_meet_first_rim
    {X ι : Type*} [MetricSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X} (F : Bool → Set X)
    (hR : IsCompact R) (he : PLDomain e R) (hF : ∀ b, F b ⊆ frontier R)
    (hFopen : IsOpen ((Subtype.val : frontier R → X) ⁻¹' F true))
    (hFdis : Disjoint (F false) (F true)) {f g : P2 → X}
    (hf : PolyhedralPLInCharts e f Ann) (hg : PolyhedralPLInCharts e g Ann)
    (hfi : InjOn f Ann) (hgi : InjOn g Ann) (hfR : MapsTo f Ann R) (hgR : MapsTo g Ann R)
    (hfp : ∀ x ∈ Ann, f x ∈ frontier R ↔ x ∈ frontier Ann)
    (hgp : ∀ x ∈ Ann, g x ∈ frontier R ↔ x ∈ frontier Ann)
    (hfmark : ∀ x ∈ Ann, f x ∈ F false ↔ depth 8 x = -1)
    (hgmark : ∀ x ∈ Ann, g x ∈ F false ↔ depth 8 x = -1)
    (hflast : MapsTo f (Ann ∩ Last) (F true)) (hglast : MapsTo g (Ann ∩ Last) (F true))
    (p : X) (hpoint : ((f '' Ann) ∩ (g '' Ann)) ∩ F false = {p})
    (hmeet : ∀ x : (Ann ∩ g ⁻¹' (f '' Ann) : Set P2), ∃ y : (Ann ∩ g ⁻¹' (f '' Ann) : Set P2),
      ConnectedComponents.mk x = ConnectedComponents.mk y ∧ (y : P2) ∈ frontier Ann)
    (hboundary : ∀ x ∈ Ann ∩ frontier Ann, f x ∈ g '' Ann →
      ∃ B : OriginalSurfacePairChart e (g '' Ann) (f '' Ann) (f x) true,
        (∀ z ∈ B.coordinates.source, B.chart.symm z ∈ R ↔ 0 ≤ (B.coordinates z).1.2) ∧
        ∀ z ∈ B.coordinates.source, B.chart.symm z ∈ frontier R ↔ (B.coordinates z).1.2 = 0)
    (hinterior : ∀ x ∈ Ann \ frontier Ann, f x ∈ g '' Ann →
      Nonempty (OriginalSurfacePairChart e (g '' Ann) (f '' Ann) (f x) false)) :
    (∀ x : (Ann ∩ g ⁻¹' (f '' Ann) : Set P2), ∃ y : (Ann ∩ g ⁻¹' (f '' Ann) : Set P2),
      ConnectedComponents.mk x = ConnectedComponents.mk y ∧ depth 8 (y : P2) = -1) ∨
    ∃ k : P2 → X, PolyhedralPLInCharts e k Ann ∧ IsEmbedding (fun x : Ann ↦ k x) ∧
      MapsTo k Ann R ∧ EqOn k f (Ann ∩ First) ∧ MapsTo k (Ann ∩ Last) (F true) ∧
      (∀ x ∈ Ann, k x ∈ frontier R ↔ x ∈ frontier Ann) ∧
      (∀ x ∈ Ann, k x ∈ F false ↔ depth 8 x = -1) ∧
      ((k '' Ann) ∩ (g '' Ann)) ∩ F false = {p} ∧
      Ann ∩ k ⁻¹' (g '' Ann) ⊆ Ann ∩ f ⁻¹' (g '' Ann) ∧
      EqOn k f (Ann ∩ k ⁻¹' (g '' Ann)) ∧
      Nat.card (ConnectedComponents (Ann ∩ k ⁻¹' (g '' Ann) : Set P2)) <
        Nat.card (ConnectedComponents (Ann ∩ f ⁻¹' (g '' Ann) : Set P2)) ∧
      (∀ x ∈ Ann ∩ frontier Ann, k x ∈ g '' Ann →
        ∃ B : OriginalSurfacePairChart e (g '' Ann) (k '' Ann) (k x) true,
          (∀ z ∈ B.coordinates.source, B.chart.symm z ∈ R ↔ 0 ≤ (B.coordinates z).1.2) ∧
          ∀ z ∈ B.coordinates.source, B.chart.symm z ∈ frontier R ↔ (B.coordinates z).1.2 = 0) ∧
      ∀ x ∈ Ann \ frontier Ann, k x ∈ g '' Ann →
        Nonempty (OriginalSurfacePairChart e (g '' Ann) (k '' Ann) (k x) false) := by
  classical
  obtain ⟨H, r, hr, hrS, hri, hrv, hinv, hd, hfront⟩ := exists_planar_annulus_reflection_map
  let f' := f ∘ r
  let g' := g ∘ r
  have hvf (x : Ann) : f' x = f (H x) := congrArg f (hrv x)
  have hvg (x : Ann) : g' x = g (H x) := congrArg g (hrv x)
  have himf : f' '' Ann = f '' Ann := image_eq_of_source_homeomorph H hvf
  have himg : g' '' Ann = g '' Ann := image_eq_of_source_homeomorph H hvg
  have hff : PolyhedralPLInCharts e f' Ann := originalPL_planar_annulus_precomposition hf hr hrS
  have hgf : PolyhedralPLInCharts e g' Ann := originalPL_planar_annulus_precomposition hg hr hrS
  have hffi : InjOn f' Ann := fun x hx y hy hxy ↦ hri hx hy (hfi (hrS hx) (hrS hy) hxy)
  have hgfi : InjOn g' Ann := fun x hx y hy hxy ↦ hri hx hy (hgi (hrS hx) (hrS hy) hxy)
  have hRim : frontier Ann = frontier spanningOuterSquare ∪ frontier spanningInnerSquare := by
    ext x
    simp only [mem_frontier_planar_annulus_iff, mem_union, spanning_outer_frontier, spanning_inner_frontier]
  have hpf' (x : P2) (hx : x ∈ Ann) : f' x ∈ frontier R ↔
      x ∈ frontier spanningOuterSquare ∪ frontier spanningInnerSquare := by
    rw [← hRim]
    exact (hfp (r x) (hrS hx)).trans (hfront x hx)
  have hpg' (x : P2) (hx : x ∈ Ann) : g' x ∈ frontier R ↔
      x ∈ frontier spanningOuterSquare ∪ frontier spanningInnerSquare := by
    rw [← hRim]
    exact (hgp (r x) (hrS hx)).trans (hfront x hx)
  have hmf' (x : P2) (hx : x ∈ Ann) : f' x ∈ F false ↔ x ∈ frontier spanningInnerSquare := by
    rw [spanning_inner_frontier]
    change f (r x) ∈ F false ↔ _
    rw [hfmark _ (hrS hx), hd x hx]
    constructor <;> intro h <;> linarith
  have hmg' (x : P2) (hx : x ∈ Ann) : g' x ∈ F false ↔ x ∈ frontier spanningInnerSquare := by
    rw [spanning_inner_frontier]
    change g (r x) ∈ F false ↔ _
    rw [hgmark _ (hrS hx), hd x hx]
    constructor <;> intro h <;> linarith
  have hlf' : MapsTo f' (Ann ∩ frontier spanningOuterSquare) (F true) := by
    intro x hx
    apply hflast
    refine ⟨hrS hx.1, ?_⟩
    change depth 8 (r x) = 1
    rw [hd x hx.1, (spanning_outer_frontier x).mp hx.2]
    norm_num
  have hlg' : MapsTo g' (Ann ∩ frontier spanningOuterSquare) (F true) := by
    intro x hx
    apply hglast
    refine ⟨hrS hx.1, ?_⟩
    change depth 8 (r x) = 1
    rw [hd x hx.1, (spanning_outer_frontier x).mp hx.2]
    norm_num
  have hpoint' : ((f' '' Ann) ∩ (g' '' Ann)) ∩ F false = {p} := by rw [himf, himg]; exact hpoint
  have hmeet' : ∀ x : (Ann ∩ g' ⁻¹' (f' '' Ann) : Set P2),
      ∃ y : (Ann ∩ g' ⁻¹' (f' '' Ann) : Set P2),
        ConnectedComponents.mk x = ConnectedComponents.mk y ∧
          (y : P2) ∈ frontier spanningOuterSquare ∪ frontier spanningInnerSquare := by
    rw [himf, ← hRim]
    apply intersection_components_meet_set_source_homeomorph H hvg _ hmeet
    intro x
    rw [← hrv x]
    exact hfront x x.property
  have hbf : ∀ x ∈ Ann, f' x ∈ g' '' Ann → f' x ∈ frontier R →
      ∃ B : OriginalSurfacePairChart e (f' '' Ann) (g' '' Ann) (f' x) true,
        (∀ z ∈ B.coordinates.source, B.chart.symm z ∈ R ↔ 0 ≤ (B.coordinates z).1.2) ∧
        ∀ z ∈ B.coordinates.source, B.chart.symm z ∈ frontier R ↔ (B.coordinates z).1.2 = 0 := by
    intro x hx hfg hb
    obtain ⟨B, hBR, hBF⟩ := hboundary (r x) ⟨hrS hx, (hfp _ (hrS hx)).mp hb⟩ (himg ▸ hfg)
    rw [himf, himg]
    exact B.swap_boundary_region hBR hBF
  have hif : ∀ x ∈ Ann, f' x ∈ g' '' Ann → f' x ∈ interior R →
      Nonempty (OriginalSurfacePairChart e (f' '' Ann) (g' '' Ann) (f' x) false) := by
    intro x hx hfg hi
    obtain ⟨B⟩ := hinterior (r x) ⟨hrS hx, fun hb ↦ ((hfp _ (hrS hx)).mpr hb).2 hi⟩ (himg ▸ hfg)
    rw [himf, himg]
    exact ⟨B.swap⟩
  obtain ⟨J, hJ, hJa⟩ := exists_planar_annulus_complex
  have hJs := hJa.trans spanning_squares_source.symm
  have hh := returning_reduction_or_components_meet_protected_rim F hR he hF hFopen hFdis
    spanningInnerSquare_ball spanningOuterSquare_ball spanning_squares_nested J hJ hJs
    (hJa.symm ▸ hff) (hJa.symm ▸ hgf) (hJa.symm ▸ hffi) (hJa.symm ▸ hgfi)
    (hJa.symm ▸ (show MapsTo f' Ann R from fun x hx ↦ hfR (hrS hx)))
    (hJa.symm ▸ (show MapsTo g' Ann R from fun x hx ↦ hgR (hrS hx)))
    (hJa.symm ▸ hpf') (hJa.symm ▸ hpg') (hJa.symm ▸ hmf') (hJa.symm ▸ hmg')
    (hJa.symm ▸ hlf') (hJa.symm ▸ hlg') p (hJa.symm ▸ hpoint')
    (hJa.symm ▸ hmeet') (hJa.symm ▸ hbf) (hJa.symm ▸ hif)
  rw [hJa] at hh
  rcases hh with hterminal | hstep
  · apply Or.inl
    rw [himf] at hterminal
    have hback (x : Ann) : g x = g' (H x) := by
      change g x = g (r (H x))
      rw [← hrv x, hinv x x.property]
    apply intersection_components_meet_set_source_homeomorph (Q := First) H hback _ hterminal
    intro x
    rw [← hrv x, spanning_inner_frontier, hd x x.property]
    change -depth 8 (x : P2) = 1 ↔ depth 8 (x : P2) = -1
    constructor <;> intro h <;> linarith
  · obtain ⟨k', hk', hki', hkR', hkH', hkF', hkp', hkm', hkpoint', hsub', hkeep',
      hcount', hkb', hki''⟩ := hstep
    let k := k' ∘ r
    have hk : PolyhedralPLInCharts e k Ann := originalPL_planar_annulus_precomposition hk' hr hrS
    have hkv (x : Ann) : k x = k' (H x) := congrArg k' (hrv x)
    have hki : IsEmbedding (fun x : Ann ↦ k x) := by
      have hv : (fun x : Ann ↦ k x) = (fun x : Ann ↦ k' x) ∘ H := funext hkv
      rw [hv]
      exact hki'.comp H.isEmbedding
    have hkimage : k '' Ann = k' '' Ann := image_eq_of_source_homeomorph H hkv
    have hkproper (x : P2) (hx : x ∈ Ann) : k x ∈ frontier R ↔ x ∈ frontier Ann := by
      exact (hkp' (r x) (hrS hx)).trans ((congrArg (fun Z : Set P2 ↦ r x ∈ Z) hRim).symm ▸ hfront x hx)
    have hkmark (x : P2) (hx : x ∈ Ann) : k x ∈ F false ↔ depth 8 x = -1 := by
      change k' (r x) ∈ F false ↔ _
      rw [hkm' _ (hrS hx), spanning_inner_frontier, hd x hx]
      constructor <;> intro h <;> linarith
    have hkFirst : EqOn k f (Ann ∩ First) := by
      intro x hx
      have hrH : r x ∈ frontier spanningInnerSquare := by
        rw [spanning_inner_frontier, hd x hx.1, show depth 8 x = -1 from hx.2]
        norm_num
      change k' (r x) = f x
      rw [hkH' ⟨hrS hx.1, hrH⟩]
      change f (r (r x)) = f x
      rw [hinv x hx.1]
    have hkLast : MapsTo k (Ann ∩ Last) (F true) := by
      intro x hx
      apply hkF'
      refine ⟨hrS hx.1, ?_⟩
      rw [spanning_outer_frontier, hd x hx.1, show depth 8 x = 1 from hx.2]
    have hkkeep : EqOn k f (Ann ∩ k ⁻¹' (g '' Ann)) := by
      intro x hx
      have hh := hkeep' ⟨hrS hx.1, show k' (r x) ∈ g' '' Ann from himg.symm ▸ hx.2⟩
      change k' (r x) = f x
      exact hh.trans (congrArg f (hinv x hx.1))
    refine Or.inr ⟨k, hk, hki, (fun x hx ↦ hkR' (hrS hx)), hkFirst, hkLast, hkproper,
      hkmark, ?_, ?_, hkkeep, ?_, ?_, ?_⟩
    · rw [hkimage, ← himg]
      exact hkpoint'
    · intro x hx
      exact ⟨hx.1, show f x ∈ g '' Ann from hkkeep hx ▸ hx.2⟩
    · rw [himg] at hcount'
      rw [intersection_component_count_source_homeomorph H (g '' Ann) hkv]
      exact hcount'.trans_eq (intersection_component_count_source_homeomorph H (g '' Ann) hvf)
    · intro x hx hxg
      obtain ⟨B, hBR, hBF⟩ := hkb' (r x) (hrS hx.1) (himg.symm ▸ hxg)
        ((hkproper x hx.1).mpr hx.2)
      rw [hkimage, ← himg]
      exact B.swap_boundary_region hBR hBF
    · intro x hx hxg
      have hi : k x ∈ interior R := by
        by_contra hn
        exact hx.2 ((hkproper x hx.1).mp ⟨subset_closure (hkR' (hrS hx.1)), hn⟩)
      obtain ⟨B⟩ := hki'' (r x) (hrS hx.1) (himg.symm ▸ hxg) hi
      rw [hkimage, ← himg]
      exact ⟨B.swap⟩

end PoincareConjecture.M76.Dehn.Annuli
