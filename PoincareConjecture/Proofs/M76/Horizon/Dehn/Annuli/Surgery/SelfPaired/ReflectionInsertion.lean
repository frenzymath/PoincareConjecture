import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.BoundaryMatchedReflectionAnnulus
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.SourceAnnulusComplement
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.SourceAnnulusFrontier
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.TargetMapPasting
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Components.Counts
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonGeometricInputs











set_option autoImplicit false

open Set Metric Geometry PLAnnularStrip
open _root_.Dehn

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem exists_reflection_insertion
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {f : P2 → X} {R : Set X}
    (J : SimplicialComplex ℝ P2) (hJ : J.faces.Finite)
    (hf : PolyhedralPLInCharts e f J.space) (he : PLDomain e R)
    (hin : MapsTo f J.space R)
    (hfront : ∀ x ∈ J.space, f x ∈ frontier R ↔ x ∈ frontier J.space)
    {L d b : ℝ} (hd : 0 < d) (hwidth : 4 * d < L) (hb : 0 < b) (hbd : b < d)
    (τ : (P2 × ℝ) → X) (hτ : PolyhedralPLInCharts e τ (singleReflectionTube L d))
    (hfib : ∀ z ∈ singleReflectionTube L d, ∀ w ∈ singleReflectionTube L d,
      τ z = τ w ↔ z = w ∨
        (z.1 = (w.1.1, -w.1.2) ∧
          ((z.2 = 0 ∧ w.2 = 2 * L) ∨ (z.2 = 2 * L ∧ w.2 = 0))))
    (hτR : τ '' singleReflectionTube L d ⊆ interior R)
    {T : Set P2} (hT : T ⊆ interior J.space)
    (c : squareAnnulus L d ≃ₜ T) (hc : c.IsFinitePL)
    (hsource : ∀ s ∈ Icc 0 (4 * L), ∀ u : Icc (-d) d,
      f (c ⟨annulusMap L (by linarith) ((s : AddCircle (4 * L)), u),
        annulus_period_point_mem hd hwidth _ u⟩) =
        if s ≤ 2 * L then τ ((u, u), s) else τ ((u, -u), s - 2 * L))
    (hpreimage : J.space ∩ f ⁻¹' (τ '' singleReflectionTube L d) = T) :
    ∃ (K : SimplicialComplex ℝ P2) (g : P2 → X),
      K.faces.Finite ∧ K.space = J.space \ interior T ∧
      K.space ∪ T = J.space ∧ K.space ∩ T = frontier T ∧
      PolyhedralPLInCharts e g J.space ∧ EqOn g f K.space ∧
      MapsTo g J.space R ∧ EqOn g f (frontier J.space) ∧
      (∀ x ∈ J.space, g x ∈ frontier R ↔ x ∈ frontier J.space) ∧
      g '' T ⊆ τ '' singleReflectionTube L d ∧
      (∀ z ∈ T, ∀ w ∈ J.space, g w = g z → w = z) ∧
      {v : P2 × P2 | v.1 ∈ J.space ∧ v.2 ∈ J.space ∧ g v.1 = g v.2 ∧ v.1 ≠ v.2} =
        {v : P2 × P2 | v.1 ∈ K.space ∧ v.2 ∈ K.space ∧ f v.1 = f v.2 ∧ v.1 ≠ v.2} ∧
      doubleLocusOn g J.space = doubleLocusOn f K.space ∧
      Disjoint K.space ((fun p : squareAnnulus L d ↦ (c p : P2)) '' {p | depth L p = 0}) := by
  have hL : 0 < L := by linarith
  obtain ⟨a, ha, haemb, haimage, hacurves, _⟩ :=
    exists_boundary_matched_reflection_annulus e he.compatible hd hwidth hb hbd τ hτ hfib
  obtain ⟨q, hq, hqval⟩ := hc.symm
  have hqmap : MapsTo q T (squareAnnulus L d) := by
    intro x hx
    rw [← hqval ⟨x, hx⟩]
    exact (c.symm ⟨x, hx⟩).property
  obtain ⟨A, hA, hAs, hAff⟩ := hq
  have haPL : PolyhedralPLInCharts e (a ∘ q) A.space :=
    ha.comp_finitePiecewiseAffineOn A hA ⟨A, hA, rfl, hAff⟩ (hAs.symm ▸ hqmap)
  have hai : InjOn (a ∘ q) A.space := by
    intro x hx y hy hxy
    have heq : q x = q y := congrArg Subtype.val
      (haemb.injective (a₁ := ⟨q x, hqmap (hAs.subset hx)⟩)
        (a₂ := ⟨q y, hqmap (hAs.subset hy)⟩) hxy)
    rw [← hqval ⟨x, hAs.subset hx⟩, ← hqval ⟨y, hAs.subset hy⟩] at heq
    exact congrArg Subtype.val (c.symm.injective (Subtype.ext heq))
  have haTube : (a ∘ q) '' A.space ⊆ τ '' singleReflectionTube L d := by
    rintro _ ⟨x, hx, rfl⟩
    exact haimage ⟨q x, hqmap (hAs.subset hx), rfl⟩
  obtain ⟨K, hK, hKs, hcover, hseam⟩ := exists_finite_interior_carrier_complement
    J A hJ hA (by rw [hAs]; exact hT)
  have hKJ : K.space ⊆ J.space := fun x hx ↦ hcover.subset (Or.inl hx)
  have hAJ : A.space ⊆ J.space := fun x hx ↦ hcover.subset (Or.inr hx)
  have hAQ : Disjoint A.space (frontier J.space) :=
    disjoint_interior_frontier.mono_left (hAs.subset.trans hT)
  have hagree : ∀ x ∈ K.space, x ∈ A.space → f x = (a ∘ q) x := by
    intro x hxK hxA
    have hxfront : x ∈ frontier T := hAs ▸ hseam.subset ⟨hxK, hxA⟩
    let p := c.symm ⟨x, hAs.subset hxA⟩
    have hcp : (c p : P2) = x := congrArg Subtype.val (c.apply_symm_apply _)
    have hpfront : (p : P2) ∈ frontier (squareAnnulus L d) :=
      (hc.mem_frontier_iff_of_finrank_eq rfl p).mp (hcp.symm ▸ hxfront)
    have hpabs := (mem_frontier_squareAnnulus_iff hd (by linarith) p.property).mp hpfront
    obtain ⟨s, hs, hsp⟩ := exists_period_parameter_of_depth hd hwidth p
    have hsourcep : f x = if s ≤ 2 * L then τ ((depth L p, depth L p), s)
        else τ ((depth L p, -depth L p), s - 2 * L) := by
      have hh := hsource s hs ⟨depth L p, mem_squareAnnulus_iff_depth.mp p.property⟩
      have hpp : (⟨annulusMap L hL ((s : AddCircle (4 * L)), depth L p),
          annulus_period_point_mem hd hwidth _
            ⟨depth L p, mem_squareAnnulus_iff_depth.mp p.property⟩⟩ : squareAnnulus L d) = p :=
        Subtype.ext hsp.symm
      simpa only [hpp, hcp] using hh
    change f x = a (q x)
    rw [← hqval ⟨x, hAs.subset hxA⟩]
    change f x = a p
    rw [hsp, hsourcep]
    rcases (abs_eq hd.le).mp hpabs with hp | hp
    · rw [hp]
      exact (hacurves s hs).2.symm
    · rw [hp]
      simpa only [neg_neg] using (hacurves s hs).1.symm
  have hcross : ∀ x ∈ A.space, ∀ y ∈ K.space, (a ∘ q) x = f y → x = y := by
    intro x hx y hy hxy
    have hyTube : f y ∈ τ '' singleReflectionTube L d := hxy ▸ haTube ⟨x, hx, rfl⟩
    have hyT : y ∈ T := hpreimage.subset ⟨hKJ hy, hyTube⟩
    exact hai hx (hAs.symm.subset hyT) (hxy.trans (hagree y hy (hAs.symm.subset hyT)))
  obtain ⟨g, hg, hgK, hgA⟩ := exists_circle_attachment_map_union he.compatible K A hK hA
    (hf.restrict_finite K hK hKJ) haPL hagree
  have hsingle : ∀ z ∈ A.space, ∀ w ∈ J.space, g w = g z → w = z := by
    intro z hz w hw hwz
    rcases hcover.symm.subset hw with hwK | hwA
    · rw [hgK hwK, hgA hz] at hwz
      exact (hcross z hz w hwK hwz.symm).symm
    · rw [hgA hwA, hgA hz] at hwz
      exact hai hwA hz hwz
  have hrel : ∀ x ∈ J.space, ∀ y ∈ J.space, x ≠ y →
      (g x = g y ↔ x ∈ K.space ∧ y ∈ K.space ∧ f x = f y) := by
    intro x hx y hy hne
    constructor
    · intro hxy
      have hxn : x ∉ A.space := fun h ↦ hne (hsingle x h y hy hxy.symm).symm
      have hyn : y ∉ A.space := fun h ↦ hne (hsingle y h x hx hxy)
      have hxK := (hcover.symm.subset hx).resolve_right hxn
      have hyK := (hcover.symm.subset hy).resolve_right hyn
      exact ⟨hxK, hyK, (hgK hxK).symm.trans (hxy.trans (hgK hyK))⟩
    · rintro ⟨hxK, hyK, hxy⟩
      rw [hgK hxK, hgK hyK]
      exact hxy
  refine ⟨K, g, hK, by simpa only [hAs] using hKs,
    by simpa only [hAs] using hcover, by simpa only [hAs] using hseam,
    hcover ▸ hg, hgK, ?_, ?_, ?_, ?_, hAs ▸ hsingle, ?_, ?_, ?_⟩
  · intro x hx
    rcases hcover.symm.subset hx with hxK | hxA
    · rw [hgK hxK]
      exact hin hx
    · rw [hgA hxA]
      exact interior_subset (hτR (haTube ⟨x, hxA, rfl⟩))
  · intro x hx
    have hxJ := (J.isCompact_space_of_finite hJ).isClosed.frontier_subset hx
    exact hgK ((hcover.symm.subset hxJ).resolve_right
      (fun hxA ↦ disjoint_left.mp hAQ hxA hx))
  · intro x hx
    rcases hcover.symm.subset hx with hxK | hxA
    · rw [hgK hxK]
      exact hfront x hx
    · rw [hgA hxA]
      exact iff_of_false
        (fun h ↦ disjoint_left.mp disjoint_interior_frontier (hτR (haTube ⟨x, hxA, rfl⟩)) h)
        (fun h ↦ disjoint_left.mp hAQ hxA h)
  · rintro y ⟨x, hx, rfl⟩
    rw [hgA (hAs.symm.subset hx)]
    exact haTube ⟨x, hAs.symm.subset hx, rfl⟩
  · ext v
    constructor
    · rintro ⟨hx, hy, hxy, hne⟩
      obtain ⟨hxK, hyK, hxyK⟩ := (hrel _ hx _ hy hne).mp hxy
      exact ⟨hxK, hyK, hxyK, hne⟩
    · rintro ⟨hx, hy, hxy, hne⟩
      exact ⟨hKJ hx, hKJ hy, (hrel _ (hKJ hx) _ (hKJ hy) hne).mpr ⟨hx, hy, hxy⟩, hne⟩
  · ext x
    constructor
    · rintro ⟨hx, y, hy, hxy, hne⟩
      obtain ⟨hxK, hyK, hxyK⟩ := (hrel _ hx _ hy hne).mp hxy
      exact ⟨hxK, y, hyK, hxyK, hne⟩
    · rintro ⟨hx, y, hy, hxy, hne⟩
      exact ⟨hKJ hx, y, hKJ hy,
        (hrel _ (hKJ hx) _ (hKJ hy) hne).mpr ⟨hx, hy, hxy⟩, hne⟩
  · apply disjoint_left.mpr
    rintro x hxK ⟨p, hp, rfl⟩
    have hpint : (p : P2) ∈ interior (squareAnnulus L d) := by
      rw [interior_squareAnnulus (by linarith)]
      change -d < depth L p ∧ depth L p < d
      rw [hp]
      exact ⟨by linarith, hd⟩
    have hxint : (c p : P2) ∈ interior T :=
      (hc.mem_interior_iff_of_finrank_eq rfl p).mpr hpint
    exact (hKs.subset hxK).2 (hAs.symm ▸ hxint)

end PoincareConjecture.M76.Dehn.Annuli
