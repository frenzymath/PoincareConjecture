import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Resolution.Tubes.OriginalCollars
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Annuli.NestedPolygonAnnulus



set_option autoImplicit false
open Set Geometry Topology PLAnnularStrip _root_.Dehn

namespace PoincareConjecture.M76.Dehn.Annuli.CircleResolution

local notation "P2" => (ℝ × ℝ)

theorem oriented_collar_middle_disk
    {L d : ℝ} {A : Set P2} (hd : 0 < d) (hwidth : 4 * d < L)
    (B : OrientedPolygonCollar L d A) {n : ℕ} (P : Polygon P2 (n + 3))
    (hP : P.HasSimplicialEdges) (hPi : Function.Injective P)
    (hmiddle : (fun p : squareAnnulus L d => (B.chart p : P2)) ''
      {p | depth L p = 0} = P.boundary ℝ) :
    closure B.inner.inside ⊆ P.inside ∧
      closure B.outer.inside ⊆ closure P.inside ∪ A := by
  let b := annulusSquare L 0 \ interior (annulusSquare L d)
  have hb (x : P2) : x ∈ b ↔ 0 ≤ depth L x ∧ depth L x ≤ d := by
    simp only [b, mem_sdiff, mem_annulusSquare_iff, mem_interior_annulusSquare_iff, not_lt]
  have hbA : b ⊆ squareAnnulus L d := by
    intro x hx
    exact mem_squareAnnulus_iff_depth.mpr ⟨by linarith [(hb x).mp hx], ((hb x).mp hx).2⟩
  have hnest : annulusSquare L d ⊆ interior (annulusSquare L 0) := by
    intro x hx
    rw [mem_interior_annulusSquare_iff]
    exact hd.trans_le ((mem_annulusSquare_iff L d x).mp hx)
  obtain ⟨c,hc,_,_⟩ := exists_square_annulus_nested_disks
    (isFinitePLBallPair_annulusSquare (by linarith : 2 * d < L))
    (isFinitePLBallPair_annulusSquare (by linarith : 2 * 0 < L))
    hnest (L := 8) (d := 1) (by norm_num) (by norm_num)
  obtain ⟨_,⟨K,hK,hKs,_⟩,_⟩ := hc.symm
  obtain ⟨f,hf,hcf⟩ := B.chart_PL
  have hfi : InjOn f (squareAnnulus L d) := by
    intro x hx y hy heq
    exact congrArg Subtype.val (B.chart.injective (Subtype.ext
      ((hcf ⟨x,hx⟩).trans (heq.trans (hcf ⟨y,hy⟩).symm))))
  have hfb : FinitePiecewiseAffineOn f b := by
    have h := hf.restrict K hK (hKs.subset.trans hbA)
    rwa [hKs] at h
  obtain ⟨e,he,hef⟩ := hfb.exists_homeomorph_image (hfi.mono hbA)
  have hcover : annulusSquare L d ∪ b = annulusSquare L 0 := by
    ext x
    rw [mem_union, mem_annulusSquare_iff, hb, mem_annulusSquare_iff]
    constructor
    · rintro (hx | hx) <;> linarith
    · intro hx
      by_cases h : d ≤ depth L x
      · exact Or.inl h
      · exact Or.inr ⟨hx,le_of_not_ge h⟩
  have hseam : annulusSquare L d ∩ b = frontier (annulusSquare L d) := by
    ext x
    rw [mem_inter_iff, mem_annulusSquare_iff, hb, mem_frontier_annulusSquare_iff]
    constructor
    · intro hx; linarith
    · intro hx; exact ⟨hx.ge,by linarith,hx.le⟩
  have hrim : frontier (annulusSquare L 0) ⊆ b := by
    intro x hx
    rw [hb, (mem_frontier_annulusSquare_iff L 0 x).mp hx]
    exact ⟨le_rfl,hd.le⟩
  have heval (x : b) : (e x : P2) = B.chart ⟨x,hbA x.property⟩ :=
    (hef x).trans (hcf ⟨x,hbA x.property⟩).symm
  have hmem (x : b) : (x : P2) ∈ frontier (annulusSquare L d) ↔
      (e x : P2) ∈ B.inner.boundary ℝ := by
    rw [heval, B.inner_depth, mem_frontier_annulusSquare_iff]
  have hcap : closure B.inner.inside ∩ f '' b = B.inner.boundary ℝ := by
    ext y
    constructor
    · rintro ⟨hy,⟨x,hx,rfl⟩⟩
      have hv : f x ∈ A := (hcf ⟨x,hbA hx⟩) ▸ (B.chart ⟨x,hbA hx⟩).property
      rw [B.carrier] at hv
      rw [closure_eq_self_union_frontier, B.inner.frontier_inside B.inner_simplicial
        B.inner_injective] at hy
      exact hy.resolve_left hv.2
    · intro hy
      have hcI := B.inner.isFinitePLBallPair_closed_inside B.inner_simplicial B.inner_injective
      have hyA : y ∈ A := by
        rw [B.carrier]
        exact ⟨subset_closure (B.nested (hcI.1 hy)), fun h => h.1 hy⟩
      let p := B.chart.symm ⟨y,hyA⟩
      have hp : (B.chart p : P2) = y := congrArg Subtype.val (B.chart.apply_symm_apply _)
      have hpdepth := (B.inner_depth p).mp (hp.symm ▸ hy)
      exact ⟨hcI.1 hy,⟨p,(hb p).mpr ⟨by linarith,hpdepth.le⟩,(hcf p).symm.trans hp⟩⟩
  have himage : f '' frontier (annulusSquare L 0) = P.boundary ℝ := by
    rw [← hmiddle]
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x,hbA (hrim hx)⟩,(mem_frontier_annulusSquare_iff L 0 x).mp hx,hcf _⟩
    · rintro ⟨p,hp,rfl⟩
      exact ⟨p,(mem_frontier_annulusSquare_iff L 0 p).mpr hp,(hcf p).symm⟩
  have hdis : Disjoint (B.inner.boundary ℝ) (P.boundary ℝ) := by
    apply Set.disjoint_left.mpr
    intro y hy hq
    rw [← hmiddle] at hq
    obtain ⟨p,hp,rfl⟩ := hq
    have hh := (B.inner_depth p).mp hy
    change depth L p = 0 at hp
    linarith
  have hball : IsFinitePLBallPair P2 (annulusSquare L d ∪ b)
      (frontier (annulusSquare L 0)) := hcover.symm ▸
    isFinitePLBallPair_annulusSquare (by linarith : 2 * 0 < L)
  obtain ⟨hinner,_⟩ := polygon_annulus_region_of_cap hball
    (isFinitePLBallPair_annulusSquare (by linarith : 2 * d < L)) hseam hrim
    B.inner P B.inner_simplicial B.inner_injective hP hPi hdis e he hmem hcap hef himage
  refine ⟨hinner,?_⟩
  intro x hx
  by_cases hi : x ∈ B.inner.inside
  · exact Or.inl (subset_closure (hinner (subset_closure hi)))
  · exact Or.inr (B.carrier.symm ▸ And.intro hx hi)

end PoincareConjecture.M76.Dehn.Annuli.CircleResolution
