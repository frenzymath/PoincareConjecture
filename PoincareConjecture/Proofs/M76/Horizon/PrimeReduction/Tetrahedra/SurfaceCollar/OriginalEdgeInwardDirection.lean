import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.AffineInteriorSlice
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.OriginalTetrahedronBall
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.LeafFields.EdgeChartHeight
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Regions.PunctureBallTriangulation










set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "W3" => ((ℝ × ℝ) × ℝ)

theorem HasOriginalEdgeCofaceCharts.exists_tetrahedron_inward_direction
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    {K : SimplicialComplex ℝ E} {g : E → X} {p q : E}
    (h : HasOriginalEdgeCofaceCharts e S K g {p,q})
    (hgi : InjOn g K.space) (hSV : Disjoint S (g '' K.vertices))
    (hpq : p ≠ q) {t : Finset E} (ht : t ∈ K.faces) (ht4 : t.card = 4)
    (hat : ({p,q} : Finset E) ⊆ t) {y : X}
    (hy : y ∈ S ∩ (g '' segment ℝ p q)) :
    ∃ (B : OpenPartialHomeomorph X V3) (V : Set V3)
      (F : W3 ≃ᴬ[ℝ] V3) (A : E →ᴬ[ℝ] V3) (w : V3),
      (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
      y ∈ B.source ∧ IsOpen V ∧ B y ∈ V ∧ V ⊆ B.target ∧ F 0 = B y ∧
      (∀ z, F z ∈ V → (B.symm (F z) ∈ S ↔ z.2 = 0)) ∧
      MapsTo g (convexHull ℝ (t : Set E)) B.source ∧
      EqOn (B ∘ g) A (convexHull ℝ (t : Set E)) ∧
      InjOn A (convexHull ℝ (t : Set E)) ∧
      w ∈ interior (A '' convexHull ℝ (t : Set E)) ∧ (F.symm w).2 = 0 := by
  classical
  have ha : ({p,q} : Finset E) ∈ K.faces :=
    K.down_closed ht hat (Finset.insert_nonempty _ _)
  have hy' : y ∈ S ∩ (g '' convexHull ℝ (({p,q} : Finset E) : Set E)) := by
    simpa only [Finset.coe_pair,convexHull_pair] using hy
  obtain ⟨B,V,F,hB,hyB,hV,hyV,hVB,hF,hFS,hFL,hco⟩ := h y hy'
  obtain ⟨hmap,A,hA⟩ := hco t ht hat
  have hTK := K.convexHull_subset_space ht
  have hseg : segment ℝ p q ⊆ convexHull ℝ (t : Set E) := by
    rw [← convexHull_pair]
    exact convexHull_mono (by simpa only [Finset.coe_pair] using Finset.coe_subset.mpr hat)
  have hAi : InjOn A (convexHull ℝ (t : Set E)) := by
    intro x hx z hz hxz
    exact hgi (hTK hx) (hTK hz)
      (B.injOn (hmap hx) (hmap hz) ((hA hx).trans (hxz.trans (hA hz).symm)))
  have hApq : A p ≠ A q := fun heq => hpq (hAi
    (hseg (left_mem_segment ℝ p q)) (hseg (right_mem_segment ℝ p q)) heq)
  have hedge : A '' segment ℝ p q = segment ℝ (A p) (A q) := image_segment ℝ A.toAffineMap p q
  have hyseg : B y ∈ segment ℝ (A p) (A q) := by
    obtain ⟨x,hx,hxy⟩ := hy.2
    rw [← hedge]
    exact ⟨x,hx,(hA (hseg hx)).symm.trans (congrArg B hxy)⟩
  have hnot (v : E) (hv : v ∈ ({p,q} : Finset E)) : B y ≠ A v := by
    intro heq
    have hvT : v ∈ convexHull ℝ (t : Set E) := subset_convexHull ℝ _ (hat hv)
    have hygv : y = g v := B.injOn hyB (hmap hvT) (heq.trans (hA hvT).symm)
    exact disjoint_left.mp hSV hy.1 ⟨v,K.face_subset_vertices ha hv,hygv.symm⟩
  have hyopen : B y ∈ openSegment ℝ (A p) (A q) :=
    mem_openSegment_of_ne_left_right (hnot p (by simp)).symm (hnot q (by simp)).symm hyseg
  have haxis (x : V3) (hx : x ∈ V) (hxs : x ∈ segment ℝ (A p) (A q)) :
      (F.symm x).1 = 0 := by
    have hphys : B.symm x ∈ g '' convexHull ℝ (({p,q} : Finset E) : Set E) := by
      obtain ⟨z,hz,hzx⟩ := hedge.symm.subset hxs
      refine ⟨z,by simpa only [Finset.coe_pair,convexHull_pair] using hz,?_⟩
      rw [← hzx,← hA (hseg hz),Function.comp_apply,B.left_inv (hmap (hseg hz))]
    exact (hFL (F.symm x) (by simpa using hx)).mp (by simpa using hphys)
  have hends := edge_chart_height_nonzero F hF hV hyV hyopen hApq haxis
  let L : V3 →ᵃ[ℝ] ℝ :=
    (LinearMap.snd ℝ (ℝ × ℝ) ℝ).toAffineMap.comp F.symm.toAffineEquiv.toAffineMap
  have hy0 : L (B y) = 0 := by
    change (F.symm (B y)).2 = 0
    rw [← hF,F.symm_apply_apply]
    rfl
  obtain ⟨u,hu,huy⟩ := (openSegment_eq_image_lineMap ℝ (A p) (A q)).symm ▸ hyopen
  have hsum : (1-u)*L (A p) + u*L (A q) = 0 := by
    rw [← huy,AffineMap.apply_lineMap,AffineMap.lineMap_apply_ring] at hy0
    exact hy0
  have hop : (L (A p) < 0 ∧ 0 < L (A q)) ∨ (L (A q) < 0 ∧ 0 < L (A p)) := by
    change L (A p) ≠ 0 ∧ L (A q) ≠ 0 at hends
    rcases lt_or_gt_of_ne hends.1 with hp | hp
    · left
      refine ⟨hp,?_⟩
      by_contra! hq
      have hn := mul_neg_of_pos_of_neg (sub_pos.mpr hu.2) hp
      have hn' := mul_nonpos_of_nonneg_of_nonpos hu.1.le hq
      linarith
    · right
      refine ⟨?_,hp⟩
      by_contra! hq
      have hn := mul_pos (sub_pos.mpr hu.2) hp
      have hn' := mul_nonneg hu.1.le hq
      linarith
  have hball := isFinitePLBallPair_independent_tetrahedron t (K.indep ht) ht4
  obtain ⟨J,_,hJ,hJs,_,_⟩ := hball.exists_finite_carrier_and_rim_complexes
  have hAPL : FinitePiecewiseAffineOn A (convexHull ℝ (t : Set E)) :=
    ⟨J,hJ,hJs,J.affineOnFaces_affine A⟩
  have himageball := hball.image hAPL hAi
  have hne := (himageball.isConnected_interior_of_finrank_eq rfl).nonempty
  have hconv : Convex ℝ (A '' convexHull ℝ (t : Set E)) :=
    (convex_convexHull ℝ _).affine_image A.toAffineMap
  have hpC : A p ∈ A '' convexHull ℝ (t : Set E) :=
    mem_image_of_mem _ (hseg (left_mem_segment ℝ p q))
  have hqC : A q ∈ A '' convexHull ℝ (t : Set E) :=
    mem_image_of_mem _ (hseg (right_mem_segment ℝ p q))
  have hex : ∃ w ∈ interior (A '' convexHull ℝ (t : Set E)), L w = 0 := by
    rcases hop with ⟨hp,hq⟩ | ⟨hq,hp⟩
    · exact exists_interior_zero_of_affine_crossing hconv hne L hpC hqC hp hq
    · exact exists_interior_zero_of_affine_crossing hconv hne L hqC hpC hq hp
  obtain ⟨w,hw,hwL⟩ := hex
  exact ⟨B,V,F,A,w,hB,hyB,hV,hyV,hVB,hF,hFS,hmap,hA,hAi,hw,hwL⟩

end PoincareConjecture.M76
