import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Resolution.Hyperbola







noncomputable section
set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.SaddleLevel

private abbrev E2 := EuclideanSpace Real (Fin 2)

variable {M : Type*} [TopologicalSpace M]

def positivePatchArc (e : OpenPartialHomeomorph E2 M) (r t : Real) (i : Fin 2) : Set M :=
  e '' (positiveLevelArc t i '' Icc (-hyperbolaRadius r t) (hyperbolaRadius r t))

def negativePatchArc (e : OpenPartialHomeomorph E2 M) (r t : Real) (i : Fin 2) : Set M :=
  e '' (negativeLevelArc t i '' Icc (-hyperbolaRadius r t) (hyperbolaRadius r t))

theorem positiveLevelArc_image_subset_square {r t : Real}
    (hr : 0 < r) (ht : 0 < t) (htr : t < r ^ 2) (i : Fin 2) :
    positiveLevelArc t i '' Icc (-hyperbolaRadius r t) (hyperbolaRadius r t) ⊆
      closedSquare r := by
  rintro x ⟨s, hs, rfl⟩
  exact (positiveLevelArc_mem_closedSquare hr ht htr i s).mpr hs

theorem negativeLevelArc_image_subset_square {r t : Real}
    (hr : 0 < r) (ht : 0 < t) (htr : t < r ^ 2) (i : Fin 2) :
    negativeLevelArc t i '' Icc (-hyperbolaRadius r t) (hyperbolaRadius r t) ⊆
      closedSquare r := by
  rintro x ⟨s, hs, rfl⟩
  exact (negativeLevelArc_mem_closedSquare hr ht htr i s).mpr hs

theorem positivePatchArc_geometry (e : OpenPartialHomeomorph E2 M) {r t : Real}
    (hr : 0 < r) (ht : 0 < t) (htr : t < r ^ 2)
    (hrs : closedSquare r ⊆ e.source) :
    (∀ i, IsCompact (positivePatchArc e r t i) ∧ IsConnected (positivePatchArc e r t i)) ∧
      Pairwise (fun i j => Disjoint (positivePatchArc e r t i) (positivePatchArc e r t j)) := by
  have hsub (i : Fin 2) := (positiveLevelArc_image_subset_square hr ht htr i).trans hrs
  have hrad := hyperbolaRadius_pos htr
  constructor
  · intro i
    exact ⟨(isCompact_positiveLevelArc_image ht i _ _).image_of_continuousOn
      (e.continuousOn.mono (hsub i)),
      ((isConnected_Icc (by linarith : -hyperbolaRadius r t ≤ hyperbolaRadius r t)).image
        (positiveLevelArc t i) (contDiff_positiveLevelArc ht i).continuous.continuousOn).image
        e (e.continuousOn.mono (hsub i))⟩
  · intro i j hij
    apply disjoint_left.mpr
    rintro q ⟨x, hx, rfl⟩ ⟨y, hy, heq⟩
    have hyx : y = x := e.injOn (hsub j hy) (hsub i hx) heq
    exact disjoint_left.mp (positiveLevelArc_pairwise_disjoint ht hij)
      (image_subset_range _ _ hx) (hyx ▸ image_subset_range _ _ hy)

theorem negativePatchArc_geometry (e : OpenPartialHomeomorph E2 M) {r t : Real}
    (hr : 0 < r) (ht : 0 < t) (htr : t < r ^ 2)
    (hrs : closedSquare r ⊆ e.source) :
    (∀ i, IsCompact (negativePatchArc e r t i) ∧ IsConnected (negativePatchArc e r t i)) ∧
      Pairwise (fun i j => Disjoint (negativePatchArc e r t i) (negativePatchArc e r t j)) := by
  have hsub (i : Fin 2) := (negativeLevelArc_image_subset_square hr ht htr i).trans hrs
  have hrad := hyperbolaRadius_pos htr
  constructor
  · intro i
    exact ⟨(isCompact_negativeLevelArc_image ht i _ _).image_of_continuousOn
      (e.continuousOn.mono (hsub i)),
      ((isConnected_Icc (by linarith : -hyperbolaRadius r t ≤ hyperbolaRadius r t)).image
        (negativeLevelArc t i) (contDiff_negativeLevelArc ht i).continuous.continuousOn).image
        e (e.continuousOn.mono (hsub i))⟩
  · intro i j hij
    apply disjoint_left.mpr
    rintro q ⟨x, hx, rfl⟩ ⟨y, hy, heq⟩
    have hyx : y = x := e.injOn (hsub j hy) (hsub i hx) heq
    exact disjoint_left.mp (negativeLevelArc_pairwise_disjoint ht hij)
      (image_subset_range _ _ hx) (hyx ▸ image_subset_range _ _ hy)

theorem positiveContact_mem_patchArc (e : OpenPartialHomeomorph E2 M) {r t : Real}
    (hr : 0 < r) (htr : t < r ^ 2) (i j : Fin 2) :
    e (positiveLevelContact r t (i, j)) ∈ positivePatchArc e r t i := by
  have hrad := hyperbolaRadius_pos htr
  apply mem_image_of_mem
  refine ⟨if j = 0 then -hyperbolaRadius r t else hyperbolaRadius r t,
    ?_, positiveLevelArc_endpoint hr htr i j⟩
  split_ifs <;> constructor <;> linarith

theorem negativeContact_mem_patchArc (e : OpenPartialHomeomorph E2 M) {r t : Real}
    (hr : 0 < r) (htr : t < r ^ 2) (i j : Fin 2) :
    e (negativeLevelContact r t (i, j)) ∈ negativePatchArc e r t i := by
  have hrad := hyperbolaRadius_pos htr
  apply mem_image_of_mem
  refine ⟨if j = 0 then -hyperbolaRadius r t else hyperbolaRadius r t,
    ?_, negativeLevelArc_endpoint hr htr i j⟩
  split_ifs <;> constructor <;> linarith

theorem positive_patch_level_eq_arcs (e : OpenPartialHomeomorph E2 M)
    {h : M → Real} {c r t : Real} (hr : 0 < r) (ht : 0 < t) (htr : t < r ^ 2)
    (hrs : closedSquare r ⊆ e.source)
    (hform : ∀ x ∈ e.source, h (e x) = c - x 0 ^ 2 + x 1 ^ 2) :
    (e '' closedSquare r) ∩ (h ⁻¹' {c + t}) = ⋃ i, positivePatchArc e r t i := by
  have heq : (e '' closedSquare r) ∩ (h ⁻¹' {c + t}) =
      e '' (closedSquare r ∩ {x : E2 | -(x 0) ^ 2 + (x 1) ^ 2 = t}) := by
    ext q
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hlevel⟩
      refine ⟨x, ⟨hx, ?_⟩, rfl⟩
      change h (e x) = c + t at hlevel
      rw [hform x (hrs hx)] at hlevel
      change -(x 0) ^ 2 + (x 1) ^ 2 = t
      linarith
    · rintro ⟨x, ⟨hx, hlevel⟩, rfl⟩
      refine ⟨⟨x, hx, rfl⟩, ?_⟩
      change h (e x) = c + t
      rw [hform x (hrs hx)]
      change -(x 0) ^ 2 + (x 1) ^ 2 = t at hlevel
      linarith
  rw [heq, closedSquare_positiveLevel_eq_arcs hr ht htr, image_iUnion]
  rfl

theorem negative_patch_level_eq_arcs (e : OpenPartialHomeomorph E2 M)
    {h : M → Real} {c r t : Real} (hr : 0 < r) (ht : 0 < t) (htr : t < r ^ 2)
    (hrs : closedSquare r ⊆ e.source)
    (hform : ∀ x ∈ e.source, h (e x) = c - x 0 ^ 2 + x 1 ^ 2) :
    (e '' closedSquare r) ∩ (h ⁻¹' {c - t}) = ⋃ i, negativePatchArc e r t i := by
  have heq : (e '' closedSquare r) ∩ (h ⁻¹' {c - t}) =
      e '' (closedSquare r ∩ {x : E2 | -(x 0) ^ 2 + (x 1) ^ 2 = -t}) := by
    ext q
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hlevel⟩
      refine ⟨x, ⟨hx, ?_⟩, rfl⟩
      change h (e x) = c - t at hlevel
      rw [hform x (hrs hx)] at hlevel
      change -(x 0) ^ 2 + (x 1) ^ 2 = -t
      linarith
    · rintro ⟨x, ⟨hx, hlevel⟩, rfl⟩
      refine ⟨⟨x, hx, rfl⟩, ?_⟩
      change h (e x) = c - t
      rw [hform x (hrs hx)]
      change -(x 0) ^ 2 + (x 1) ^ 2 = -t at hlevel
      linarith
  rw [heq, closedSquare_negativeLevel_eq_arcs hr ht htr, image_iUnion]
  rfl


theorem positive_level_eq_arcs_union_exterior (e : OpenPartialHomeomorph E2 M)
    {h : M → Real} {c r t : Real} (hr : 0 < r) (ht : 0 < t) (htr : t < r ^ 2)
    (hrs : closedSquare r ⊆ e.source)
    (hform : ∀ x ∈ e.source, h (e x) = c - x 0 ^ 2 + x 1 ^ 2) :
    h ⁻¹' {c + t} = (⋃ i, positivePatchArc e r t i) ∪
      ((h ⁻¹' {c + t}) \ e '' openSquare r) := by
  rw [← positive_patch_level_eq_arcs e hr ht htr hrs hform]
  have hsub := image_mono (f := e) (openSquare_subset_closedSquare r)
  ext q
  constructor
  · intro hq
    by_cases hp : q ∈ e '' openSquare r
    · exact Or.inl ⟨hsub hp, hq⟩
    · exact Or.inr ⟨hq, hp⟩
  · rintro (hq | hq)
    · exact hq.2
    · exact hq.1

theorem negative_level_eq_arcs_union_exterior (e : OpenPartialHomeomorph E2 M)
    {h : M → Real} {c r t : Real} (hr : 0 < r) (ht : 0 < t) (htr : t < r ^ 2)
    (hrs : closedSquare r ⊆ e.source)
    (hform : ∀ x ∈ e.source, h (e x) = c - x 0 ^ 2 + x 1 ^ 2) :
    h ⁻¹' {c - t} = (⋃ i, negativePatchArc e r t i) ∪
      ((h ⁻¹' {c - t}) \ e '' openSquare r) := by
  rw [← negative_patch_level_eq_arcs e hr ht htr hrs hform]
  have hsub := image_mono (f := e) (openSquare_subset_closedSquare r)
  ext q
  constructor
  · intro hq
    by_cases hp : q ∈ e '' openSquare r
    · exact Or.inl ⟨hsub hp, hq⟩
    · exact Or.inr ⟨hq, hp⟩
  · rintro (hq | hq)
    · exact hq.2
    · exact hq.1

theorem positivePatchArc_inter_exterior_subset_contacts (e : OpenPartialHomeomorph E2 M)
    {h : M → Real} {c r t : Real} (hr : 0 < r) (ht : 0 < t) (htr : t < r ^ 2)
    (i : Fin 2) :
    positivePatchArc e r t i ∩ ((h ⁻¹' {c + t}) \ e '' openSquare r) ⊆
      range (fun j : Fin 2 × Fin 2 => e (positiveLevelContact r t j)) := by
  rintro q ⟨⟨x, ⟨s, hs, rfl⟩, rfl⟩, _, hnot⟩
  have hboundary : positiveLevelArc t i s ∈ closedSquare r \ openSquare r :=
    ⟨(positiveLevelArc_mem_closedSquare hr ht htr i s).mpr hs,
      fun hx => hnot (mem_image_of_mem e hx)⟩
  rcases (positiveLevelArc_boundary_iff hr ht htr i s).mp hboundary with he | he
  · exact ⟨(i, 0), congrArg e (by simpa [he] using (positiveLevelArc_endpoint hr htr i 0).symm)⟩
  · exact ⟨(i, 1), congrArg e (by simpa [he] using (positiveLevelArc_endpoint hr htr i 1).symm)⟩

theorem negativePatchArc_inter_exterior_subset_contacts (e : OpenPartialHomeomorph E2 M)
    {h : M → Real} {c r t : Real} (hr : 0 < r) (ht : 0 < t) (htr : t < r ^ 2)
    (i : Fin 2) :
    negativePatchArc e r t i ∩ ((h ⁻¹' {c - t}) \ e '' openSquare r) ⊆
      range (fun j : Fin 2 × Fin 2 => e (negativeLevelContact r t j)) := by
  rintro q ⟨⟨x, ⟨s, hs, rfl⟩, rfl⟩, _, hnot⟩
  have hboundary : negativeLevelArc t i s ∈ closedSquare r \ openSquare r :=
    ⟨(negativeLevelArc_mem_closedSquare hr ht htr i s).mpr hs,
      fun hx => hnot (mem_image_of_mem e hx)⟩
  rcases (negativeLevelArc_boundary_iff hr ht htr i s).mp hboundary with he | he
  · exact ⟨(i, 0), congrArg e (by simpa [he] using (negativeLevelArc_endpoint hr htr i 0).symm)⟩
  · exact ⟨(i, 1), congrArg e (by simpa [he] using (negativeLevelArc_endpoint hr htr i 1).symm)⟩

end Poincare.Manifold.Schoenflies.SaddleLevel
