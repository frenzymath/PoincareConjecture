import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Coordinates.PlanePairSignTransport
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.LeafFields.OriginalTriangleEdgeGerm
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Affine.PlaneHeight

set_option autoImplicit false

open Set Geometry Module Filter
open scoped Topology

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "W3" => ((ℝ × ℝ) × ℝ)

theorem HasOriginalEdgeCofaceCharts.exists_triangle_mixed_signs_in_chart
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    {K : SimplicialComplex ℝ E} {g : E → X} {s a : Finset E}
    (h : HasOriginalEdgeCofaceCharts e S K g a)
    (hs : s ∈ K.faces) (hs3 : s.card = 3) (has : a ⊆ s) (ha2 : a.card = 2)
    (hgi : InjOn g K.space) (hSV : Disjoint S (g '' K.vertices))
    {y : X} (hy : y ∈ S ∩ (g '' convexHull ℝ (a : Set E)))
    (Q : OpenPartialHomeomorph X V3) (A : E →ᴬ[ℝ] V3)
    (hmap : MapsTo g (convexHull ℝ (s : Set E)) Q.source)
    (hA : EqOn (Q ∘ g) A (convexHull ℝ (s : Set E)))
    (L : V3 →ᵃ[ℝ] ℝ) (hL : L.linear ≠ 0)
    (hLplane : ∀ x, L x = 0 ↔ x ∈ affineSpan ℝ (A '' (s : Set E))) :
    ∃ U : Set V3, IsOpen U ∧ Q y ∈ U ∧ U ⊆ Q.target ∧
      ∀ x ∈ (Q '' (S ∩ Q.source) ∩
        intrinsicInterior ℝ (convexHull ℝ (A '' (s : Set E)))) ∩ U,
        x ∈ closure ((Q '' (S ∩ Q.source)) ∩ {z | L z < 0}) ∧
          x ∈ closure ((Q '' (S ∩ Q.source)) ∩ {z | 0 < L z}) := by
  classical
  obtain ⟨B, V, F, _, hyB, hV, hyV, hVB, hF, hFS, hFL, hco⟩ := h y hy
  obtain ⟨hRmap, R, hR⟩ := hco s hs has
  let D := convexHull ℝ (s : Set E)
  have hDne : D.Nonempty := (K.nonempty_of_mem_faces hs).to_set.convexHull
  have hDi (C : OpenPartialHomeomorph X V3) (T : E →ᴬ[ℝ] V3)
      (hm : MapsTo g D C.source) (he : EqOn (C ∘ g) T D) : InjOn T D := by
    intro x hx z hz hxz
    exact hgi (K.convexHull_subset_space hs hx) (K.convexHull_subset_space hs hz)
      (C.injOn (hm hx) (hm hz) ((he hx).trans (hxz.trans (he hz).symm)))
  have hAi := hDi Q A hmap hA
  have hRi := hDi B R hRmap hR
  have hAsp := A.toAffineMap.injOn_affineSpan_of_injOn_convex
    (convex_convexHull ℝ _) hDne hAi
  have hRsp := R.toAffineMap.injOn_affineSpan_of_injOn_convex
    (convex_convexHull ℝ _) hDne hRi
  have hAR : A '' D = convexHull ℝ (A '' (s : Set E)) := A.toAffineMap.image_convexHull _
  have hRR : R '' D = convexHull ℝ (R '' (s : Set E)) := R.toAffineMap.image_convexHull _
  have hRdim : finrank ℝ (affineSpan ℝ (R '' (s : Set E))).direction = 2 := by
    have hi := R.toAffineMap.affineIndependent_comp_of_injOn_convexHull
      (p := ((↑) : s → E)) (K.indep hs) (by rw [Subtype.range_coe]; exact hRi)
    have hrange : range (R.toAffineMap ∘ ((↑) : s → E)) = R '' (s : Set E) := by
      rw [range_comp, Subtype.range_coe]
      rfl
    have hh := hi.finrank_vectorSpan (n := 2) (by simpa using hs3)
    rw [hrange] at hh
    rw [direction_affineSpan]
    exact hh
  obtain ⟨H, hH, hHplane⟩ :=
    (affineSpan ℝ (R '' (s : Set E))).exists_defining_height_of_finrank_two
      (by simp) hRdim ((hDne.image R).mono (by
        rw [hRR]; exact convexHull_subset_affineSpan _))
  let C : V3 →ᵃ[ℝ] ℝ := (LinearMap.snd ℝ (ℝ × ℝ) ℝ).toAffineMap.comp
    F.symm.toAffineEquiv.toAffineMap
  have hyedge : y ∈ g '' D := image_mono (convexHull_mono has) hy.2
  obtain ⟨y₀, hy₀, hgy₀⟩ := hyedge
  have hyQ : y ∈ Q.source := hgy₀ ▸ hmap hy₀
  have htransverse : ∃ u, H u = 0 ∧ C u ≠ 0 := by
    obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.mp ha2
    have hsegsub : segment ℝ p q ⊆ D := by
      rw [← convexHull_pair]
      apply convexHull_mono
      intro z hz
      exact has (by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff,
        Finset.mem_insert, Finset.mem_singleton] using hz)
    have hphysical (z : V3) (hz : z ∈ B.target) :
        B.symm z ∈ g '' segment ℝ p q ↔ z ∈ segment ℝ (R p) (R q) := by
      have himage : (B ∘ g) '' segment ℝ p q = segment ℝ (R p) (R q) := by
        rw [image_congr (fun x hx => hR (hsegsub hx))]
        exact image_segment ℝ R.toAffineMap p q
      constructor
      · rintro ⟨u, hu, hgu⟩
        rw [← himage]
        exact ⟨u, hu, by change B (g u) = z; rw [hgu, B.right_inv hz]⟩
      · intro hzt
        obtain ⟨u, hu, huz⟩ := himage.symm.subset hzt
        exact ⟨u, hu, by rw [← huz]; exact (B.left_inv (hRmap (hsegsub hu))).symm⟩
    have hypq : B y ∈ segment ℝ (R p) (R q) :=
      (hphysical _ (B.map_source hyB)).mp (by
        simpa only [B.left_inv hyB, Finset.coe_pair, convexHull_pair] using hy.2)
    have hpvert : p ∈ K.vertices := K.face_subset_vertices hs (has (by simp))
    have hqvert : q ∈ K.vertices := K.face_subset_vertices hs (has (by simp))
    have hpy : R p ≠ B y := by
      intro hp
      have he := B.injOn (hRmap (hsegsub (left_mem_segment ℝ p q))) hyB
        ((hR (hsegsub (left_mem_segment ℝ p q))).trans hp)
      exact disjoint_left.mp hSV hy.1 ⟨p, hpvert, he⟩
    have hqy : R q ≠ B y := by
      intro hq
      have he := B.injOn (hRmap (hsegsub (right_mem_segment ℝ p q))) hyB
        ((hR (hsegsub (right_mem_segment ℝ p q))).trans hq)
      exact disjoint_left.mp hSV hy.1 ⟨q, hqvert, he⟩
    have hRpq : R p ≠ R q := fun he => hpq (hRi
      (hsegsub (left_mem_segment ℝ p q)) (hsegsub (right_mem_segment ℝ p q)) he)
    have haxis : ∀ z ∈ V, z ∈ segment ℝ (R p) (R q) → (F.symm z).1 = 0 := by
      intro z hzV hzt
      have hh := hFL (F.symm z) (by simpa only [F.apply_symm_apply] using hzV)
      apply hh.mp
      simpa only [F.apply_symm_apply, Finset.coe_pair, convexHull_pair] using
        (hphysical z (hVB hzV)).mpr hzt
    have hends := edge_chart_height_nonzero F hF hV hyV
      (mem_openSegment_of_ne_left_right hpy hqy hypq) hRpq haxis
    refine ⟨R p, (hHplane _).mpr ?_, hends.1⟩
    exact subset_affineSpan ℝ _ (mem_image_of_mem R (has (by simp)))
  obtain ⟨u, huH, huC⟩ := htransverse
  let f := B.symm.trans Q
  have hyf : B y ∈ f.source := by
    change B y ∈ B.target ∧ B.symm (B y) ∈ Q.source
    exact ⟨B.map_source hyB, by simpa only [B.left_inv hyB] using hyQ⟩
  have hfy : f (B y) = Q y := by change Q (B.symm (B y)) = Q y; rw [B.left_inv hyB]
  let U := f.target ∩ f.symm ⁻¹' V
  have hU : IsOpen U := f.symm.isOpen_inter_preimage hV
  have hyU : Q y ∈ U := by
    rw [← hfy]
    refine ⟨f.map_source hyf, ?_⟩
    change f.symm (f (B y)) ∈ V
    simpa only [f.left_inv hyf] using hyV
  refine ⟨U, hU, hyU, fun x hx => hx.1.1, ?_⟩
  rintro x ⟨⟨hxS, hxi⟩, hxU⟩
  let b := f.symm x
  have hbf : b ∈ f.source := f.map_target hxU.1
  have hfb : f b = x := f.right_inv hxU.1
  have hbV : b ∈ V := hxU.2
  have hbC : C b = 0 := by
    obtain ⟨z, ⟨hzS, hzQ⟩, hzx⟩ := hxS
    have hphys : B.symm b = z := Q.injOn hbf.2 hzQ (hfb.trans hzx.symm)
    have hh := hFS (F.symm b) (by simpa only [F.apply_symm_apply] using hbV)
    exact hh.mp (by simpa only [F.apply_symm_apply, hphys] using hzS)
  have hxim : x ∈ intrinsicInterior ℝ (A '' D) := hAR.symm ▸ hxi
  change x ∈ intrinsicInterior ℝ (A.toAffineMap '' D) at hxim
  rw [A.toAffineMap.intrinsicInterior_image_of_injOn_span D hAsp] at hxim
  obtain ⟨z, hzi, hzx⟩ := hxim
  have hzD := intrinsicInterior_subset hzi
  have hbR : b = R z := by
    apply B.symm.injOn hbf.1 (by rw [← hR hzD]; exact B.map_source (hRmap hzD))
    rw [← hR hzD, Function.comp_apply, B.left_inv (hRmap hzD)]
    exact Q.injOn hbf.2 (hmap hzD) (hfb.trans (hzx.symm.trans (hA hzD).symm))
  have hbi : b ∈ intrinsicInterior ℝ (R '' D) := by
    change b ∈ intrinsicInterior ℝ (R.toAffineMap '' D)
    rw [R.toAffineMap.intrinsicInterior_image_of_injOn_span D hRsp, hbR]
    exact mem_image_of_mem R hzi
  have hbH : H b = 0 := (hHplane b).mpr
    (convexHull_subset_affineSpan _ (hRR.subset (intrinsicInterior_subset hbi)))
  have hpair (v : V3) (hv : v ∈ f.source) : v ∈ R '' D ↔ f v ∈ A '' D := by
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, by
        change A z = Q (B.symm (R z))
        rw [← hR hz, Function.comp_apply, B.left_inv (hRmap hz)]
        exact (hA hz).symm⟩
    · rintro ⟨z, hz, hzfv⟩
      have he : B.symm v = g z := Q.injOn hv.2 (hmap hz)
        (hzfv.symm.trans (hA hz).symm)
      exact ⟨z, hz, by rw [← hR hz, Function.comp_apply, ← he, B.right_inv hv.1]⟩
  have hgerm : ∀ᶠ v in 𝓝 b, H v = 0 ↔ L (f v) = 0 := by
    have hBgerm := eventually_mem_iff_mem_affineSpan_of_intrinsicInterior hbi
    have hQgerm := (f.continuousAt hbf).eventually
      (hfb.symm ▸ eventually_mem_iff_mem_affineSpan_of_intrinsicInterior
        (hAR.symm ▸ hxi))
    filter_upwards [hBgerm, hQgerm, f.open_source.mem_nhds hbf] with v hvB hvQ hvf
    have hBspan : affineSpan ℝ (R '' D) = affineSpan ℝ (R '' (s : Set E)) := by
      rw [hRR, affineSpan_convexHull]
    have hQspan : affineSpan ℝ (A '' D) = affineSpan ℝ (A '' (s : Set E)) := by
      rw [hAR, affineSpan_convexHull]
    rw [hBspan] at hvB
    rw [hQspan] at hvQ
    exact (hHplane v).trans (hvB.symm.trans ((hpair v hvf).trans
      (hvQ.trans (hLplane (f v)).symm)))
  obtain ⟨O, hOsub, hO, hbO⟩ := mem_nhds_iff.mp hgerm
  have hsigns := H.mem_closure_both_signs_on_zero_plane C hH hbH hbC huH huC
  let Z := {v | C v = 0} ∩ V
  have hn : b ∈ closure (Z ∩ {v | H v < 0}) := by
    apply closure_mono (s := ({v | C v = 0} ∩ {v | H v < 0}) ∩ V)
      (t := Z ∩ {v | H v < 0})
      (fun v hv => ⟨⟨hv.1.1, hv.2⟩, hv.1.2⟩)
    exact hV.closure_inter ⟨hsigns.1, hbV⟩
  have hp : b ∈ closure (Z ∩ {v | 0 < H v}) := by
    apply closure_mono (s := ({v | C v = 0} ∩ {v | 0 < H v}) ∩ V)
      (t := Z ∩ {v | 0 < H v})
      (fun v hv => ⟨⟨hv.1.1, hv.2⟩, hv.1.2⟩)
    exact hV.closure_inter ⟨hsigns.2, hbV⟩
  have hxL : L (f b) = 0 := by
    rw [hfb]
    exact (hLplane x).mpr (convexHull_subset_affineSpan _ (intrinsicInterior_subset hxi))
  have htransport := f.mem_closure_both_signs_of_plane_germ H L hL hbf hxL hO hbO
    (fun v hv => hOsub hv.1) hn hp
  have hsub : f '' (Z ∩ f.source) ⊆ Q '' (S ∩ Q.source) := by
    rintro _ ⟨v, ⟨⟨hvC, hvV⟩, hvf⟩, rfl⟩
    refine ⟨B.symm v, ⟨?_, hvf.2⟩, rfl⟩
    have hh := hFS (F.symm v) (by simpa only [F.apply_symm_apply] using hvV)
    simpa only [F.apply_symm_apply] using hh.mpr hvC
  rw [hfb] at htransport
  exact ⟨closure_mono (inter_subset_inter_left _ hsub) htransport.1,
    closure_mono (inter_subset_inter_left _ hsub) htransport.2⟩

end PoincareConjecture.M76
