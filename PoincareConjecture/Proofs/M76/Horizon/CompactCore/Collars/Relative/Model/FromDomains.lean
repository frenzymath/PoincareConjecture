import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.Relative.Model.SurfaceStars
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.Relative.Model.FiniteDomainPair
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.Relative.Charts.SignedPair
import PoincareConjecture.Proofs.M76.Rigidity.MarkedMixedChartStars
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.OriginalDiskStarNeighborhood



set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

attribute [local instance] Classical.propDecidable

local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)




theorem exists_cooriented_surface_stars_of_domains
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {D W : Set X}
    (hD : IsCompact D) (heD : PLDomain e D)
    (hW : IsCompact W) (heW : PLDomain e W) (hne : (D ∪ W).Nonempty)
    (hcross : ∀ x ∈ frontier D ∩ frontier W,
      ∃ B : OpenPartialHomeomorph X V3,
        x ∈ B.source ∧ B x = 0 ∧
        (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
        (∀ y ∈ B.source, y ∈ frontier D ↔ B y 0 = 0) ∧
        ∀ y ∈ B.source, y ∈ frontier W ↔ B y 1 = 0) :
    ∃ (s : Finset (D ∪ W : Set X)) (F : X → (s → ℝ × V3)) (C : Set X)
      (T : SimplicialComplex.CoorientedSurfaceStars (s → ℝ × V3))
      (H : C ≃ₜ T.ambient.space) (g : (s → ℝ × V3) → C)
      (B : (T.marked 2).vertices → OpenPartialHomeomorph X C3),
      IsCompact C ∧ D ∪ W ⊆ interior C ∧ Continuous F ∧
      (∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target) ∧
      T.ambient.space = F '' C ∧
      (T.marked 0).space = F '' W ∧
      (T.marked 1).space = F '' frontier W ∧
      (T.marked 2).space = F '' (frontier D ∩ W) ∧
      (T.marked 3).space = F '' (frontier D ∩ frontier W) ∧
      (∀ x : C, (H x : s → ℝ × V3) = F x) ∧
      ContinuousOn g T.ambient.space ∧
      (∀ z : T.ambient.space, (g z : X) = (H.symm z : X)) ∧
      PolyhedralPLInCharts e (fun z ↦ (g z : X)) T.ambient.space ∧
      (∀ x ∈ C, ∃ (i : ι) (V : Set X) (a : (s → ℝ × V3) →ᴬ[ℝ] V3),
        IsOpen V ∧ x ∈ V ∧ V ⊆ (e i).source ∧ EqOn (a ∘ F) (e i) V) ∧
      ∀ p : (T.marked 2).vertices,
        (∀ z, T.chart p z = B p (g z)) ∧
        (∀ i, LocallyPiecewiseAffineOn ((e i).symm.trans (B p))
          ((e i).symm.trans (B p)).source) ∧
        MapsTo (fun z ↦ (g z : X)) (T.ambient.closedStar p).space (B p).source ∧
        (∀ z ∈ (T.ambient.closedStar p).space, (g z : X) ∈ D ↔ 0 ≤ (T.chart p z).2) ∧
        ∀ z ∈ (T.ambient.closedStar p).space,
          (g z : X) ∈ frontier D ↔ (T.chart p z).2 = 0 := by
  classical
  obtain ⟨s, F, C, K, A, H0, g, hC, hDC, hFc, hF, hK, hA,
    hKs, hA0, hA1, hA2, hA3, hmeet, hHF, hgc, hg, hgPL, hproj⟩ :=
    exists_finite_relative_frontier_model hD heD hW heW hne
  have hFinj : InjOn F C := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (H0.injective (Subtype.ext
      ((hHF ⟨x, hx⟩).trans (hxy.trans (hHF ⟨y, hy⟩).symm))))
  have hgF (z) (hz : z ∈ K.space) : F (g z) = z := by
    rw [hg ⟨z, hz⟩]
    exact (hHF (H0.symm ⟨z, hz⟩)).symm.trans
      (congrArg Subtype.val (H0.apply_symm_apply ⟨z, hz⟩))
  have hmem (S : Set X) (hSC : S ⊆ C) (z) (hz : z ∈ K.space) :
      z ∈ F '' S ↔ (g z : X) ∈ S := by
    constructor
    · rintro ⟨y, hy, heq⟩
      have hyz : y = (g z : X) :=
        hFinj (hSC hy) (g z).property (heq.trans (hgF z hz).symm)
      exact hyz ▸ hy
    · intro hzS
      exact ⟨g z, hzS, hgF z hz⟩
  have hWC : W ⊆ C := fun _ hx ↦ interior_subset (hDC (Or.inr hx))
  have hFWC : frontier W ⊆ C := heW.closed.frontier_subset.trans hWC
  have hSWC : frontier D ∩ W ⊆ C := inter_subset_right.trans hWC
  have hSpoint (q : (A 2).space) : (g q : X) ∈ frontier D ∩ W :=
    (hmem _ hSWC q (SimplicialComplex.space_subset_of_le (hA 2).1 q.property)).mp
      (hA2.subset q.property)
  choose G hGpoint hGzero hGe hGD hGf hGW using fun q : (A 2).space ↦
    heD.exists_signed_relative_frontier_chart heW hcross (hSpoint q)
  obtain ⟨R, L, hR, hRK, hL, hstars⟩ :=
    hgPL.exists_full_marked_mixed_chart_stars K hK
      ((A 2).isCompact_space_of_finite (hA 2).2.1)
      (SimplicialComplex.space_subset_of_le (hA 2).1)
      G hGe hGpoint (fun _ ↦ univ) (fun _ ↦ isOpen_univ) (fun _ ↦ mem_univ _)
      A (fun i ↦ (hA i).2.1)
      (fun i ↦ SimplicialComplex.space_subset_of_le (hA i).1)
  let H : C ≃ₜ R.space := H0.trans (Homeomorph.setCongr hRK.space_eq.symm)
  have hg' (z : R.space) : (g z : X) = (H.symm z : X) :=
    hg ⟨z, hRK.space_eq.subset z.property⟩
  have hL0 : (L 0).space = F '' W := (hL 0).2.1.trans hA0
  have hL1 : (L 1).space = F '' frontier W := (hL 1).2.1.trans hA1
  have hL2 : (L 2).space = F '' (frontier D ∩ W) := (hL 2).2.1.trans hA2
  have hL3 : (L 3).space = F '' (frontier D ∩ frontier W) := (hL 3).2.1.trans hA3
  have hstarK (p : (L 2).vertices) : (R.closedStar p).space ⊆ K.space := by
    have hs : R.closedStar p ≤ R := fun _ hs ↦ hs.1
    exact (SimplicialComplex.space_subset_of_le hs).trans hRK.space_eq.subset
  have hchoose (p : (L 2).vertices) : ∃ q : (A 2).space,
      MapsTo (fun z ↦ (g z : X)) (R.closedStar p).space (G q).source ∧
      (R.closedStar p).AffineOnFaces (G q ∘ fun z ↦ (g z : X)) := by
    have hpR : (p : s → ℝ × V3) ∈ R.vertices := (hL 2).1 p.property
    have hpA : (p : s → ℝ × V3) ∈ (A 2).space :=
      (hL 2).2.1.subset ((L 2).vertices_subset_space p.property)
    obtain ⟨q, _, hsource, hface⟩ := hstars p hpR hpA
    exact ⟨q, hsource, hface⟩
  choose q hsource hface using hchoose
  let B (p : (L 2).vertices) := G (q p)
  let c (p : (L 2).vertices) : (s → ℝ × V3) → C3 := fun z ↦ B p (g z)
  have hnormal (p : (L 2).vertices) (z) (hz : z ∈ (R.closedStar p).space) :
      (g z : X) ∈ D ↔ 0 ≤ (c p z).2 := hGD (q p) _ (hsource p hz)
  have hzero (p : (L 2).vertices) (z) (hz : z ∈ (R.closedStar p).space) :
      (g z : X) ∈ frontier D ↔ (c p z).2 = 0 := hGf (q p) _ (hsource p hz)
  have hmodel0 (p : (L 2).vertices) (z) (hz : z ∈ (R.closedStar p).space) :
      z ∈ (L 0).space ↔ (g z : X) ∈ W := by
    rw [hL0]
    exact hmem W hWC z (hstarK p hz)
  have hmodel1 (p : (L 2).vertices) (z) (hz : z ∈ (R.closedStar p).space) :
      z ∈ (L 1).space ↔ (g z : X) ∈ frontier W := by
    rw [hL1]
    exact hmem _ hFWC z (hstarK p hz)
  have hmodel2 (p : (L 2).vertices) (z) (hz : z ∈ (R.closedStar p).space) :
      z ∈ (L 2).space ↔ (g z : X) ∈ frontier D ∩ W := by
    rw [hL2]
    exact hmem _ hSWC z (hstarK p hz)
  have hlocal (p : (L 2).vertices) :
      InjOn (c p) (R.closedStar p).space ∧
      c p p ∈ interior (c p '' (R.closedStar p).space) := by
    have hpR : (p : s → ℝ × V3) ∈ R.vertices := (hL 2).1 p.property
    have hpA : (p : s → ℝ × V3) ∈ (A 2).space :=
      (hL 2).2.1.subset ((L 2).vertices_subset_space p.property)
    have hpC : (g p : X) ∈ interior C := hDC (Or.inr (hSpoint ⟨p, hpA⟩).2)
    obtain ⟨hinj, _, hint⟩ := R.exists_original_open_neighborhood_inside_closedStar
      hR H g hg' hpR hpC (B p) (hsource p)
    exact ⟨hinj, hint⟩
  let T : SimplicialComplex.CoorientedSurfaceStars (s → ℝ × V3) :=
    { ambient := R
      marked := L
      finite := hR
      marked_le := fun i ↦ (hL i).1
      marked_full := fun i ↦ (hL i).2.2
      boundary_subset_region := by
        rw [hL1, hL0]
        exact image_mono heW.closed.frontier_subset
      surface_subset_region := by
        rw [hL2, hL0]
        exact image_mono inter_subset_right
      surface_boundary_inter := by
        rw [(hL 2).2.1, (hL 1).2.1, (hL 3).2.1]
        exact hmeet
      chart := c
      star_affine := hface
      star_injective := fun p ↦ (hlocal p).1
      star_interior := fun p ↦ (hlocal p).2
      chart_model := by
        intro p
        rcases hGW (q p) with hi | hb
        · left
          refine ⟨fun z hz ↦ (hmodel0 p z hz).mpr (interior_subset (hi.2 (hsource p hz))), ?_⟩
          apply disjoint_left.mpr
          intro z hz hzb
          exact (hmodel1 p z hz).mp hzb |>.2 (hi.2 (hsource p hz))
        · right
          exact ⟨fun z hz ↦ (hmodel0 p z hz).trans (hb.2.1 _ (hsource p hz)),
            fun z hz ↦ (hmodel1 p z hz).trans (hb.2.2 _ (hsource p hz))⟩
      surface_eq := by
        intro p z hz
        rw [hmodel2 p z hz, hmodel0 p z hz]
        exact and_comm.trans (and_congr_right fun _ ↦ hzero p z hz)
      nonneg_agree := fun p q z hp hq ↦ (hnormal p z hp).symm.trans (hnormal q z hq)
      zero_agree := fun p q z hp hq ↦ (hzero p z hp).symm.trans (hzero q z hq) }
  refine ⟨s, F, C, T, H, g, B, hC, hDC, hFc, hF,
    hRK.space_eq.trans hKs, hL0, hL1, hL2, hL3, hHF,
    hRK.space_eq.symm ▸ hgc, hg', hRK.space_eq.symm ▸ hgPL, hproj, ?_⟩
  intro p
  exact ⟨fun _ ↦ rfl, hGe (q p), hsource p, hnormal p, hzero p⟩

end PoincareConjecture.M76
