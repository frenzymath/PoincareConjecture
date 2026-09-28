import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Whole.EdgeStars
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.LeafFields.OriginalEdgeCofaceCharts
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.LeafFields.EdgeChartHeight








set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76
local notation "V2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

theorem HasOriginalEdgeCofaceCharts.exists_whole_planar_edge_crossing
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (K : SimplicialComplex ℝ V2) (hK : K.faces.Finite)
    {g : V2 → X} (hgc : ContinuousOn g K.space) (hgi : InjOn g K.space)
    (hSV : Disjoint S (g '' K.vertices))
    {p q x : V2} (hpq : p ≠ q) (hs : ({p, q} : Finset V2) ∈ K.faces)
    (h : HasOriginalEdgeCofaceCharts e S K g {p, q})
    (hx : x ∈ intrinsicInterior ℝ (convexHull ℝ ({p, q} : Set V2)))
    (hxK : x ∈ interior K.space) (hgx : g x ∈ S)
    {N : Set X} (hN : IsOpen N) (hgxN : g x ∈ N) :
    ∃ (B : OpenPartialHomeomorph X V3) (H : OpenPartialHomeomorph V3 C3),
      (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
      g x ∈ B.source ∧ B (g x) ∈ H.source ∧
      H.source ⊆ B.target ∩ B.symm ⁻¹' N ∧ H (B (g x)) = 0 ∧
      LocallyPiecewiseAffineOn H H.source ∧
      LocallyPiecewiseAffineOn H.symm H.target ∧
      (∀ z ∈ H.source, B.symm z ∈ S ↔ (H z).2 = 0) ∧
      ∀ z ∈ H.source, B.symm z ∈ g '' K.space ↔ (H z).1.1 = 0 := by
  classical
  have hx' : x ∈ intrinsicInterior ℝ (convexHull ℝ (({p, q} : Finset V2) : Set V2)) := by
    simpa only [Finset.coe_pair] using hx
  obtain ⟨B, V, F, hB, hxB, hV, hxV, hVB, hF, hFS, hFL, hco⟩ :=
    h (g x) ⟨hgx, x, intrinsicInterior_subset hx', rfl⟩
  obtain ⟨hT, hTK, hxT, hmapT, hfaces, hcoord, W, hW, hxW, hwhole⟩ :=
    K.exists_original_coface_star_image_germ hK hgc hgi hs hx' hxK B hco
  have hsp : p ∈ K.space := K.subset_space hs (by simp)
  have hsq : q ∈ K.space := K.subset_space hs (by simp)
  obtain ⟨hmap, D, hD⟩ := hco {p, q} hs (Finset.Subset.refl _)
  have hpHull : p ∈ convexHull ℝ (({p, q} : Finset V2) : Set V2) :=
    subset_convexHull ℝ _ (by simp)
  have hqHull : q ∈ convexHull ℝ (({p, q} : Finset V2) : Set V2) :=
    subset_convexHull ℝ _ (by simp)
  have hDp : B (g p) = D p := hD hpHull
  have hDq : B (g q) = D q := hD hqHull
  have hedge : (B ∘ g) '' segment ℝ p q = segment ℝ (D p) (D q) := by
    calc
      _ = D.toAffineMap '' segment ℝ p q := image_congr (fun u hu => hD
        (by simpa only [Finset.coe_pair, convexHull_pair] using hu))
      _ = _ := image_segment ℝ D.toAffineMap p q
  have hphysical (z : V3) (hz : z ∈ B.target) :
      B.symm z ∈ g '' segment ℝ p q ↔ z ∈ segment ℝ (D p) (D q) := by
    rw [← hedge]
    constructor
    · rintro ⟨u, hu, heq⟩
      exact ⟨u, hu, (congrArg B heq).trans (B.right_inv hz)⟩
    · rintro ⟨u, hu, heq⟩
      have huB : g u ∈ B.source := hmap (by
        simpa only [Finset.coe_pair, convexHull_pair] using hu)
      exact ⟨u, hu, (B.left_inv huB).symm.trans (congrArg B.symm heq)⟩
  have hxseg : B (g x) ∈ segment ℝ (D p) (D q) :=
    (hphysical _ (B.map_source hxB)).mp (by
      rw [B.left_inv hxB]
      exact ⟨x, by simpa only [convexHull_pair] using intrinsicInterior_subset hx, rfl⟩)
  have hpne : D p ≠ B (g x) := by
    intro heq
    have hh : g p = g x := B.injOn (hmap hpHull) hxB (hDp.trans heq)
    exact disjoint_left.mp hSV hgx ⟨p, K.face_subset_vertices hs (by simp), hh⟩
  have hqne : D q ≠ B (g x) := by
    intro heq
    have hh : g q = g x := B.injOn (hmap hqHull) hxB (hDq.trans heq)
    exact disjoint_left.mp hSV hgx ⟨q, K.face_subset_vertices hs (by simp), hh⟩
  have hpqD : D p ≠ D q := by
    intro heq
    exact hpq (hgi hsp hsq (B.injOn (hmap hpHull) (hmap hqHull)
      (hDp.trans (heq.trans hDq.symm))))
  have haxis (z : V3) (hz : z ∈ V) (hze : z ∈ segment ℝ (D p) (D q)) :
      (F.symm z).1 = 0 := by
    have hh := hFL (F.symm z) (by simpa only [F.apply_symm_apply] using hz)
    apply hh.mp
    simpa only [F.apply_symm_apply, Finset.coe_pair, convexHull_pair] using
      (hphysical z (hVB hz)).mpr hze
  have hends := edge_chart_height_nonzero F hF hV hxV
    (mem_openSegment_of_ne_left_right hpne hqne hxseg) hpqD haxis
  let height : V3 →ᵃ[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ V2 ℝ).toContinuousAffineMap.toAffineMap.comp
      F.symm.toAffineEquiv.toAffineMap
  have hzero : height (B (g x)) = 0 := by
    change (F.symm (B (g x))).2 = 0
    rw [← hF, F.symm_apply_apply]
    rfl
  let O := V ∩ (B.target ∩ B.symm ⁻¹' (W ∩ N))
  have hO : IsOpen O := hV.inter (B.symm.isOpen_inter_preimage (hW.inter hN))
  have hxO : B (g x) ∈ O := by
    refine ⟨hxV, B.map_source hxB, ?_⟩
    change B.symm (B (g x)) ∈ W ∩ N
    rw [B.left_inv hxB]
    exact ⟨hxW, hgxN⟩
  have hsT : ({p, q} : Finset V2) ∈ (K.closedFaceStar {p, q}).faces :=
    ⟨hs, by simpa using hs⟩
  obtain ⟨H, hxH, hHO, hHzero, hHPL, hHinv, hsurface, hheight⟩ :=
    hfaces.exists_planar_image_edge_crossing (K.closedFaceStar {p, q}) hT hcoord hsT
      (by simp [hpq]) hx' hxT height hzero (by
        refine ⟨p, by simp, ?_⟩
        change (F.symm (B (g p))).2 ≠ 0
        rw [hDp]
        exact hends.1) hO hxO
  refine ⟨B, H, hB, hxB, hxH, fun z hz => ⟨(hHO hz).2.1, (hHO hz).2.2.2⟩,
    hHzero, hHPL, hHinv, ?_, ?_⟩
  · intro z hz
    have hh := hFS (F.symm z) (by simpa only [F.apply_symm_apply] using (hHO hz).1)
    have hh' : B.symm z ∈ S ↔ height z = 0 := by
      change B.symm z ∈ S ↔ (F.symm z).2 = 0
      simpa only [F.apply_symm_apply] using hh
    exact hh'.trans (by rw [hheight z hz])
  · intro z hz
    rw [hwhole _ (hHO hz).2.2.1]
    have heq : B.symm z ∈ g '' (K.closedFaceStar {p, q}).space ↔
        z ∈ (B ∘ g) '' (K.closedFaceStar {p, q}).space := by
      constructor
      · rintro ⟨u, hu, heq⟩
        exact ⟨u, hu, (congrArg B heq).trans (B.right_inv (hHO hz).2.1)⟩
      · rintro ⟨u, hu, heq⟩
        exact ⟨u, hu, (B.left_inv (hmapT hu)).symm.trans (congrArg B.symm heq)⟩
    exact heq.trans (hsurface z hz)

end PoincareConjecture.M76
