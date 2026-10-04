import PoincareLib.Topology.Manifold.Smoothing.Dehn.Annuli.Surgery.Collars.ContractibleBoundary

/-!
# Compressing a contractible collar inside an annular source

Extend the actual collar's depth-reflected whole boundary map over its
inner disk. The complementary source copy is the literal identity. Their
images form the original annulus, with exactly the prescribed common seam;
the hole and both original rims are disjoint from the inserted disk.
-/

set_option autoImplicit false
open Set Geometry PLAnnularStrip
open _root_.Dehn

namespace PoincareMT.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)

theorem exists_contractible_collar_source_compression
    {A : Set P2} {l r L d : ℝ} (B : OrientedPolygonCollar l r A)
    (hr : 0 < r) (hwidth : 4 * r < l)
    (hcontract : closure B.outer.inside ⊆ {p : P2 | -d < depth L p ∧ depth L p < d}) :
    ∃ (eb : B.inner.boundary ℝ ≃ₜ B.outer.boundary ℝ)
      (H : closure B.inner.inside ≃ₜ closure B.outer.inside) (j : P2 → P2),
      eb.IsFinitePL ∧ H.IsFinitePL ∧ FinitePiecewiseAffineOn j (closure B.inner.inside) ∧
      (∀ x : closure B.inner.inside, j x = (H x : P2)) ∧
      Topology.IsEmbedding (fun x : closure B.inner.inside ↦ j x) ∧
      j '' closure B.inner.inside = closure B.outer.inside ∧
      (∀ x : B.inner.boundary ℝ, j x = (eb x : P2)) ∧
      (∀ (s : ℝ) (_hs : s ∈ Icc 0 (4 * l)),
        j (B.chart ⟨annulusMap l (by linarith)
          ((s : AddCircle (4 * l)), r), annulus_period_point_mem hr hwidth _
            ⟨r, by constructor <;> linarith⟩⟩) =
        B.chart ⟨annulusMap l (by linarith)
          ((s : AddCircle (4 * l)), -r), annulus_period_point_mem hr hwidth _
            ⟨-r, by constructor <;> linarith⟩⟩) ∧
      (∀ x ∈ closure B.inner.inside, ∀ y ∈ squareAnnulus L d \ B.outer.inside,
        j x = y ↔ ∃ hx : x ∈ B.inner.boundary ℝ, (eb ⟨x, hx⟩ : P2) = y) ∧
      j '' closure B.inner.inside ∪ (squareAnnulus L d \ B.outer.inside) = squareAnnulus L d ∧
      j '' closure B.inner.inside ∩ (squareAnnulus L d \ B.outer.inside) = B.outer.boundary ℝ ∧
      Disjoint (closure B.inner.inside) (squareAnnulus L d \ B.outer.inside) ∧
      frontier (annulusSquare L (-d)) ∪ frontier (annulusSquare L d) ⊆
        squareAnnulus L d \ B.outer.inside ∧
      Disjoint (j '' closure B.inner.inside)
        (frontier (annulusSquare L (-d)) ∪ frontier (annulusSquare L d)) ∧
      Disjoint (j '' closure B.inner.inside) (annulusSquare L d) ∧
      squareAnnulus L d \ (closure B.inner.inside ∪ (squareAnnulus L d \ B.outer.inside)) =
        B.outer.inside \ closure B.inner.inside := by
  obtain ⟨eb, heb, hperiod⟩ := exists_collar_inner_outer_boundary_homeomorph B hr hwidth
  have hp := B.outer.isFinitePLBallPair_closed_inside B.outer_simplicial B.outer_injective
  have hi := B.inner.isFinitePLBallPair_closed_inside B.inner_simplicial B.inner_injective
  obtain ⟨H, hH, hHb, hHmem⟩ := hi.exists_extension hp eb heb
  obtain ⟨j, hj, hHj⟩ := hH
  have himage : j '' closure B.inner.inside = closure B.outer.inside := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [← hHj ⟨x, hx⟩]
      exact (H ⟨x, hx⟩).property
    · intro hy
      refine ⟨H.symm ⟨y, hy⟩, (H.symm ⟨y, hy⟩).property, ?_⟩
      rw [← hHj, H.apply_symm_apply]
  have hboundary (x : B.inner.boundary ℝ) : j x = (eb x : P2) := by
    have hx := congrArg Subtype.val (hHb x)
    rwa [hHj] at hx
  have hPs : closure B.outer.inside ⊆ squareAnnulus L d := fun x hx ↦
    mem_squareAnnulus_iff_depth.mpr ⟨(hcontract hx).1.le, (hcontract hx).2.le⟩
  have hcontact : j '' closure B.inner.inside ∩ (squareAnnulus L d \ B.outer.inside) =
      B.outer.boundary ℝ := by
    rw [himage, ← B.outer.frontier_inside B.outer_simplicial B.outer_injective,
      frontier, (B.outer.isOpen_inside B.outer_simplicial B.outer_injective).interior_eq]
    ext x
    exact ⟨fun hx ↦ ⟨hx.1, hx.2.2⟩, fun hx ↦ ⟨hx.1, hPs hx.1, hx.2⟩⟩
  have hd : 0 < d := by
    have h := hcontract (hp.1 (B.outer.vertex_mem_boundary 0))
    linarith [h.1, h.2]
  have hrim : frontier (annulusSquare L (-d)) ∪ frontier (annulusSquare L d) ⊆
      squareAnnulus L d \ B.outer.inside := by
    intro x hx
    have he : depth L x = -d ∨ depth L x = d :=
      hx.imp ((mem_frontier_annulusSquare_iff L (-d) x).mp)
        ((mem_frontier_annulusSquare_iff L d x).mp)
    refine ⟨mem_squareAnnulus_iff_depth.mpr (by rcases he with h | h <;> constructor <;> linarith), ?_⟩
    intro hin
    have hh := hcontract (subset_closure hin)
    rcases he with h | h <;> linarith [hh.1, hh.2]
  refine ⟨eb, H, j, heb, ⟨j, hj, hHj⟩, hj, fun x ↦ (hHj x).symm, ?_, himage,
    hboundary, ?_, ?_, ?_, hcontact, ?_, hrim, ?_, ?_, ?_⟩
  · have hfun : (fun x : closure B.inner.inside ↦ j x) =
        fun x : closure B.inner.inside ↦ (H x : P2) := funext fun x ↦ (hHj x).symm
    rw [hfun]
    exact Topology.IsEmbedding.subtypeVal.comp H.isEmbedding
  · intro s hs
    exact (hboundary ⟨_, (B.inner_depth _).mpr (depth_annulusMap (by linarith)
      (by simpa only [abs_of_pos hr] using hwidth) _)⟩).trans (hperiod s hs)
  · intro x hx y hy
    constructor
    · intro heq
      have hyb : j x ∈ B.outer.boundary ℝ := hcontact ▸
        ⟨mem_image_of_mem j hx, heq.symm ▸ hy⟩
      have hxb : x ∈ B.inner.boundary ℝ := (hHmem ⟨x, hx⟩).mpr (by rwa [hHj])
      exact ⟨hxb, (hboundary ⟨x, hxb⟩).symm.trans heq⟩
    · rintro ⟨hxb, heq⟩
      exact (hboundary ⟨x, hxb⟩).trans heq
  · rw [himage]
    apply Subset.antisymm (union_subset hPs sdiff_subset)
    intro x hx
    by_cases hin : x ∈ B.outer.inside
    · exact Or.inl (subset_closure hin)
    · exact Or.inr ⟨hx, hin⟩
  · exact disjoint_left.mpr fun x hx hy ↦ hy.2 (B.nested hx)
  · rw [himage]
    apply disjoint_left.mpr
    intro x hx hy
    have hh := hcontract hx
    rcases hy with hy | hy
    · have he := (mem_frontier_annulusSquare_iff L (-d) x).mp hy
      linarith [hh.1]
    · have he := (mem_frontier_annulusSquare_iff L d x).mp hy
      linarith [hh.2]
  · rw [himage]
    exact disjoint_left.mpr fun x hx hy ↦
      (not_lt_of_ge ((mem_annulusSquare_iff L d x).mp hy)) (hcontract hx).2
  · ext x
    constructor
    · rintro ⟨hx, hn⟩
      exact ⟨by by_contra h; exact hn (Or.inr ⟨hx, h⟩), fun h ↦ hn (Or.inl h)⟩
    · rintro ⟨hx, hn⟩
      exact ⟨hPs (subset_closure hx), fun h ↦ h.elim hn (fun he ↦ he.2 hx)⟩

end PoincareMT.M76.Dehn.Annuli
