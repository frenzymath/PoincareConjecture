import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Contractible.Disjoint.Source
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Contractible.Disjoint.TubeSeams
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Contractible.CollarDiskMap









set_option autoImplicit false
open Set Geometry PLAnnularStrip
open _root_.Dehn

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem exists_disjoint_contractible_map
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    (e : ι → OpenPartialHomeomorph X V3)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (J : SimplicialComplex ℝ P2) (hJ : J.faces.Finite)
    {A : Fin 2 → Set P2} {L d b : ℝ} (B : ∀ k, OrientedPolygonCollar L d (A k))
    (hcontract : ∀ k, closure (B k).outer.inside ⊆ interior J.space)
    (hdis : Disjoint (closure (B 0).outer.inside) (closure (B 1).outer.inside))
    (hd : 0 < d) (hwidth : 4 * d < L) (hb : 0 < b) (hbd : b < d)
    (f : P2 → X) (hf : PolyhedralPLInCharts e f J.space)
    (τ : C3 → X) (hτ : PolyhedralPLInCharts e τ (identityTube L d))
    (hfib : ∀ z ∈ identityTube L d, ∀ w ∈ identityTube L d,
      τ z = τ w ↔ z.1 = w.1 ∧
        (z.2 : AddCircle (4 * L)) = (w.2 : AddCircle (4 * L)))
    (hvalue : ∀ (k : Fin 2) (s : ℝ) (_hs : s ∈ Icc 0 (4 * L)) (u : Icc (-d) d),
      f ((B k).chart ⟨annulusMap L (by linarith) ((s : AddCircle (4 * L)), u),
        annulus_period_point_mem hd hwidth _ u⟩) = τ (sourceTubeDiagonal k u, s)) :
    ∃ (H : closure (B 0).inner.inside ≃ₜ closure (B 1).inner.inside)
      (a : Fin 2 → P2 → X) (g : P2 → X),
      H.IsFinitePL ∧
      (∀ x : closure (B 0).inner.inside,
        (H x : P2) ∈ (B 1).inner.boundary ℝ ↔ (x : P2) ∈ (B 0).inner.boundary ℝ) ∧
      (∀ k, Topology.IsEmbedding (fun p : squareAnnulus L d ↦ a k p)) ∧
      (∀ k, PolyhedralPLInCharts e (a k) (squareAnnulus L d)) ∧
      (∀ k, a k '' squareAnnulus L d ⊆ τ '' identityTube L d) ∧
      Disjoint (a 0 '' squareAnnulus L d) (a 1 '' squareAnnulus L d) ∧
      PolyhedralPLInCharts e g J.space ∧
      (∀ x : closure (B 0).inner.inside, g (H x) = f x) ∧
      (∀ x : closure (B 1).inner.inside, g (H.symm x) = f x) ∧
      EqOn g f (J.space \ ((B 0).outer.inside ∪ (B 1).outer.inside)) ∧
      EqOn g f (frontier J.space) ∧
      (∀ k (p : squareAnnulus L d), g ((B k).chart p) = a k p) ∧
      g '' J.space = ((f '' closure (B 0).inner.inside ∪ f '' closure (B 1).inner.inside) ∪
        f '' (J.space \ ((B 0).outer.inside ∪ (B 1).outer.inside))) ∪
          (a 0 '' squareAnnulus L d ∪ a 1 '' squareAnnulus L d) := by
  classical
  obtain ⟨H, hH, hHb, hHperiod, hHsymm⟩ := exists_synchronized_inner_disk_exchange (B 0) (B 1)
  obtain ⟨O, hO, hOs, hrim⟩ := exists_disjoint_contractible_exterior J hJ (B 0) (B 1)
    (hcontract 0) (hcontract 1) hdis
  obtain ⟨a, haemb, haPL, haTube, hadis, haouter, hainner⟩ :=
    exists_disjoint_resolving_annuli_retained_seams e hcompat hd hwidth hb hbd A
      (fun k ↦ (B k).chart) f τ hτ hfib hvalue
  have hI (k : Fin 2) := (B k).inner.isFinitePLBallPair_closed_inside
    (B k).inner_simplicial (B k).inner_injective
  have hP (k : Fin 2) := (B k).outer.isFinitePLBallPair_closed_inside
    (B k).outer_simplicial (B k).outer_injective
  have hIsub (k : Fin 2) : closure (B k).inner.inside ⊆ J.space :=
    (B k).nested.trans (subset_closure.trans ((hcontract k).trans interior_subset))
  have hfI (k : Fin 2) : PolyhedralPLInCharts e f (closure (B k).inner.inside) := by
    obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hI k
    simpa only [hKs] using hf.restrict_finite K hK (hKs.subset.trans (hIsub k))
  obtain ⟨v₀, hv₀, hv₀I, hv₀A, hv₀P, hv₀image⟩ :=
    exists_collar_disk_map e hcompat (B 0) (B 1) H.symm hH.symm hHsymm f (a 0)
      (hfI 1) (haPL 0) (haouter 0) (hainner 0)
  obtain ⟨v₁, hv₁, hv₁I, hv₁A, hv₁P, hv₁image⟩ :=
    exists_collar_disk_map e hcompat (B 1) (B 0) H hH hHperiod f (a 1)
      (hfI 0) (haPL 1) (haouter 1) (hainner 1)
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨P₀, hP₀, hPs₀, _⟩, _⟩, _⟩ := hP 0
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨P₁, hP₁, hPs₁, _⟩, _⟩, _⟩ := hP 1
  obtain ⟨v, hv, hv0, hv1⟩ := exists_circle_attachment_map_union hcompat P₀ P₁ hP₀ hP₁
    (by simpa only [hPs₀] using hv₀) (by simpa only [hPs₁] using hv₁)
    (fun x hx hy ↦ (disjoint_left.mp hdis (hPs₀.subset hx) (hPs₁.subset hy)).elim)
  obtain ⟨P, hPf, hPs⟩ := P₀.exists_finite_triangulation_union P₁ hP₀ hP₁
  have hseam₀ : closure (B 0).outer.inside ∩ O.space = (B 0).outer.boundary ℝ := by
    rw [hOs, ← (B 0).outer.frontier_inside (B 0).outer_simplicial (B 0).outer_injective,
      frontier, ((B 0).outer.isOpen_inside (B 0).outer_simplicial (B 0).outer_injective).interior_eq]
    ext x
    constructor
    · exact fun hx ↦ ⟨hx.1, fun h ↦ hx.2.2 (Or.inl h)⟩
    · intro hx
      refine ⟨hx.1, interior_subset (hcontract 0 hx.1), ?_⟩
      rintro (h | h)
      · exact hx.2 h
      · exact disjoint_left.mp hdis hx.1 (subset_closure h)
  have hseam₁ : closure (B 1).outer.inside ∩ O.space = (B 1).outer.boundary ℝ := by
    rw [hOs, ← (B 1).outer.frontier_inside (B 1).outer_simplicial (B 1).outer_injective,
      frontier, ((B 1).outer.isOpen_inside (B 1).outer_simplicial (B 1).outer_injective).interior_eq]
    ext x
    constructor
    · exact fun hx ↦ ⟨hx.1, fun h ↦ hx.2.2 (Or.inr h)⟩
    · intro hx
      refine ⟨hx.1, interior_subset (hcontract 1 hx.1), ?_⟩
      rintro (h | h)
      · exact disjoint_left.mp hdis (subset_closure h) hx.1
      · exact hx.2 h
  obtain ⟨g, hg, hgv, hgo⟩ := exists_circle_attachment_map_union hcompat P O hPf hO
    (by simpa only [hPs] using hv) (hf.restrict_finite O hO (hOs.subset.trans sdiff_subset)) (by
      intro x hx ho
      rcases hPs.subset hx with hx | hx
      · exact (hv0 hx).trans (hv₀P (hseam₀.subset ⟨hPs₀.subset hx, ho⟩))
      · exact (hv1 hx).trans (hv₁P (hseam₁.subset ⟨hPs₁.subset hx, ho⟩)))
  have hdom : P.space ∪ O.space = J.space := by
    rw [hPs, hPs₀, hPs₁, hOs]
    apply Subset.antisymm
      (union_subset (union_subset ((hcontract 0).trans interior_subset)
        ((hcontract 1).trans interior_subset)) sdiff_subset)
    intro x hx
    by_cases h : x ∈ (B 0).outer.inside ∪ (B 1).outer.inside
    · exact Or.inl (h.imp (fun h ↦ subset_closure h) (fun h ↦ subset_closure h))
    · exact Or.inr ⟨hx, h⟩
  have hg0 (x : P2) (hx : x ∈ closure (B 0).outer.inside) : g x = v₀ x :=
    (hgv (hPs.symm.subset (Or.inl (hPs₀.symm.subset hx)))).trans (hv0 (hPs₀.symm.subset hx))
  have hg1 (x : P2) (hx : x ∈ closure (B 1).outer.inside) : g x = v₁ x :=
    (hgv (hPs.symm.subset (Or.inr (hPs₁.symm.subset hx)))).trans (hv1 (hPs₁.symm.subset hx))
  have hgI0 (x : closure (B 0).inner.inside) : g (H x) = f x :=
    (hg1 _ (subset_closure ((B 1).nested (H x).property))).trans (hv₁I x)
  have hgI1 (x : closure (B 1).inner.inside) : g (H.symm x) = f x :=
    (hg0 _ (subset_closure ((B 0).nested (H.symm x).property))).trans (hv₀I x)
  have hgA (k : Fin 2) (p : squareAnnulus L d) : g ((B k).chart p) = a k p := by
    fin_cases k
    · exact (hg0 _ ((B 0).carrier.subset ((B 0).chart p).property).1).trans (hv₀A p)
    · exact (hg1 _ ((B 1).carrier.subset ((B 1).chart p).property).1).trans (hv₁A p)
  refine ⟨H, a, g, hH, hHb, haemb, haPL, haTube, hadis, hdom ▸ hg, hgI0, hgI1,
    fun x hx ↦ hgo (hOs.symm.subset hx), fun x hx ↦ hgo (hrim hx), hgA, ?_⟩
  have hgi0 : g '' closure (B 0).outer.inside = v₀ '' closure (B 0).outer.inside :=
    image_congr hg0
  have hgi1 : g '' closure (B 1).outer.inside = v₁ '' closure (B 1).outer.inside :=
    image_congr hg1
  conv_lhs =>
    rw [← hdom, image_union, hPs, image_union, hPs₀, hPs₁, hgi0, hgi1,
      hv₀image, hv₁image, image_congr hgo, hOs]
  ac_rfl

end PoincareConjecture.M76.Dehn.Annuli
