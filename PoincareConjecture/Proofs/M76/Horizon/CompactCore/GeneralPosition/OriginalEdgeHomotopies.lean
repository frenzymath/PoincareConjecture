import PoincareConjecture.Proofs.M76.Horizon.CompactCore.GeneralPosition.ProtectedEdgeHomotopies

set_option autoImplicit false

open Set Metric Geometry Geometry.SimplicialComplex unitInterval

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem PLDomain.exists_original_edge_homotopies
    {E X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [DecidableEq E] [TopologicalSpace X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3} {N Y F : Set X}
    (hN : PLDomain e N) (hY : IsOpen Y) (hcut : Y ∩ frontier N = F)
    (K : SimplicialComplex ℝ E) (f : E → X) (hfY : MapsTo f K.space Y)
    (a b : κ → K.vertices)
    (hedges : ∀ k, {(a k : E), (b k : E)} ∈ K.faces)
    (B : κ → OpenPartialHomeomorph X V3)
    (hcompat : ∀ k i, (e i).symm.trans (B k) ∈ piecewiseAffineGroupoid V3)
    (hsource : ∀ k, MapsTo f (K.closedStar (a k)).space (B k).source)
    (hcoord : ∀ k, (K.closedStar (a k)).AffineOnFaces (B k ∘ f))
    (U : κ → Set X) (hU : ∀ k, IsOpen (U k))
    (hfU : ∀ k, MapsTo f (segment ℝ (a k : E) (b k : E)) (U k)) :
    ∃ (p : K.vertices → C(I, X)) (H : κ → C(I × I, X))
      (q : κ → ℝ → X),
      (∀ v, p v 0 = f v) ∧ (∀ v t, p v t ∈ Y) ∧
      (∀ v : K.vertices, f v ∉ F → ∀ t, p v t = f v) ∧
      (∀ v (t : I), 0 < (t : ℝ) → p v t ∉ F) ∧
      (∀ k z, H k z ∈ U k) ∧
      (∀ k t, H k (t, 0) = p (a k) t ∧ H k (t, 1) = p (b k) t) ∧
      (∀ k s, H k (0, s) = f (AffineMap.lineMap (a k : E) (b k : E) (s : ℝ))) ∧
      (∀ k s, H k (1, s) = q k s) ∧
      (∀ k, PolyhedralPLInCharts e (q k) (Icc (0 : ℝ) 1)) ∧
      ∀ k t s, B k (H k (t, s)) =
        AffineMap.lineMap (B k (p (a k) t)) (B k (p (b k) t)) (s : ℝ) := by
  classical
  have hface (k : κ) : {(a k : E), (b k : E)} ∈ (K.closedStar (a k)).faces := by
    refine ⟨hedges k, ?_⟩
    simpa only [Finset.insert_eq_of_mem (Finset.mem_insert_self _ _)] using hedges k
  have hstar (k : κ) : segment ℝ (a k : E) (b k : E) ⊆
      (K.closedStar (a k)).space := by
    simpa only [Finset.coe_pair, convexHull_pair] using convexHull_subset_space (hface k)
  choose A hA using fun k => hcoord k _ (hface k)
  have hEq (k : κ) : EqOn (B k ∘ f) (A k) (segment ℝ (a k : E) (b k : E)) := by
    simpa only [Finset.coe_pair, convexHull_pair] using hA k
  have hline (k : κ) (s : I) :
      B k (f (AffineMap.lineMap (a k : E) (b k : E) (s : ℝ))) =
        AffineMap.lineMap (B k (f (a k))) (B k (f (b k))) (s : ℝ) := by
    rw [show B k (f (AffineMap.lineMap (a k : E) (b k : E) (s : ℝ))) =
      A k (AffineMap.lineMap (a k : E) (b k : E) (s : ℝ)) from
        hEq k (lineMap_mem_segment ℝ _ _ s.property)]
    calc
      A k (AffineMap.lineMap (a k : E) (b k : E) (s : ℝ)) =
          AffineMap.lineMap (A k (a k)) (A k (b k)) (s : ℝ) :=
        (A k).toAffineMap.apply_lineMap _ _ _
      _ = _ := by
        rw [← hEq k (left_mem_segment ℝ _ _), ← hEq k (right_mem_segment ℝ _ _)]
        rfl
  have hedge (k : κ) : segment ℝ (B k (f (a k))) (B k (f (b k))) ⊆
      (B k).target ∩ (B k).symm ⁻¹' U k := by
    rw [segment_eq_image_lineMap]
    rintro _ ⟨s, hs, rfl⟩
    rw [← hline k ⟨s, hs⟩]
    have hm := lineMap_mem_segment ℝ (a k : E) (b k : E) hs
    have hz := hsource k (hstar k hm)
    exact ⟨(B k).map_source hz, by simpa only [mem_preimage, (B k).left_inv hz] using hfU k hm⟩
  obtain ⟨p, H, hp0, hpY, hpfix, hpoff, hHU, hend, hformula, hcoords, hPL, hstart⟩ :=
    hN.exists_protected_edge_homotopies hY hcut B a b (fun v : K.vertices => f v)
      hcompat (fun v => hfY (vertices_subset_space v.property)) U hU
      (fun k => hsource k (hstar k (left_mem_segment ℝ _ _)))
      (fun k => hsource k (hstar k (right_mem_segment ℝ _ _))) hedge
  refine ⟨p, H, fun k => (B k).symm ∘
    AffineMap.lineMap (B k (p (a k) 1)) (B k (p (b k) 1)),
    hp0, hpY, hpfix, hpoff, hHU, hend, ?_, fun k s => hformula k 1 s, hPL, hcoords⟩
  intro k s
  rw [hstart, ← hline k s]
  exact (B k).left_inv (hsource k (hstar k (lineMap_mem_segment ℝ _ _ s.property)))

end PoincareConjecture.M76
