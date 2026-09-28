import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Faces.Coordinates.OriginalNormalFamily
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Faces.Coordinates.AffineRegionTransport
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Faces.Counting.SuccessorRectangleFamily










set_option autoImplicit false
open Set Geometry TriangularRoofModel
namespace PoincareConjecture.M76.PrismBelt
open TriangleCorner

theorem exists_original_successor_rectangles_with_contacts
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Finite ι]
    (K : SimplicialComplex ℝ E) {s : Finset E} (hs : s ∈ K.faces) (hs3 : s.card = 3)
    (d r : ι → Set E) (hd : ∀ i, IsFinitePLBallPair ℝ (d i) (r i))
    (hsub : ∀ i, d i ⊆ convexHull ℝ (s : Set E))
    (hrim : ∀ i, r i = d i ∩ intrinsicFrontier ℝ (convexHull ℝ (s : Set E)))
    (hdis : Pairwise fun i j => Disjoint (d i) (d j))
    (hvertex : ∀ i, Disjoint (d i) (s : Set E))
    (hnr : ∀ i, ∀ t : Finset E, t ⊆ s → t.card = 2 → ¬ r i ⊆ convexHull ℝ (t : Set E)) :
    ∃ (F : (ℝ × ℝ) →ᴬ[ℝ] E) (R : E →ᴬ[ℝ] (ℝ × ℝ))
      (c : ι → Fin 3) (a b : ι → ℝ),
      Function.LeftInverse R F ∧
      EqOn (F ∘ R) id (convexHull ℝ (s : Set E)) ∧
      F '' base = convexHull ℝ (s : Set E) ∧
      F '' vertices = (s : Set E) ∧
      F '' frontier base = intrinsicFrontier ℝ (convexHull ℝ (s : Set E)) ∧
      (∀ i, a i ∈ Ioo (0 : ℝ) 1) ∧ (∀ i, b i ∈ Ioo (0 : ℝ) 1) ∧
      (∀ i, r i = F '' (cornerMap (c i) '' ({(0,b i),(a i,0)} : Set (ℝ × ℝ)))) ∧
      Nat.card {i : ι // ∃ j, c j = c i ∧ a i < a j} + Nat.card (range c) = Nat.card ι ∧
      Nat.card (range c) ≤ 3 ∧
      ∃ (n : {i : ι // ∃ j, c j = c i ∧ a i < a j} → ι)
        (M : {i : ι // ∃ j, c j = c i ∧ a i < a j} → Set E),
        Function.Injective M ∧
        ∀ i, c (n i) = c i ∧ a i < a (n i) ∧
          IsFinitePLBallPair (ℝ × ℝ) (M i)
            (d i ∪ (d (n i) ∪ F '' (cornerMap (c i) '' edgeIntervals (a i) (b i) (a (n i)) (b (n i))))) ∧
          M i ∩ intrinsicFrontier ℝ (convexHull ℝ (s : Set E)) =
            F '' (cornerMap (c i) '' edgeIntervals (a i) (b i) (a (n i)) (b (n i))) ∧
          (∀ k : ι, k ≠ (i : ι) → k ≠ n i → Disjoint (d k) (M i)) ∧
          M i ∩ (⋃ k, d k) = d i ∪ d (n i) ∧
          (∀ x ∈ M i \ (d i ∪ d (n i)),
            connectedComponentIn (convexHull ℝ (s : Set E) \ ⋃ k, d k) x = M i \ (d i ∪ d (n i)) ∧
            closure (connectedComponentIn (convexHull ℝ (s : Set E) \ ⋃ k, d k) x) = M i) ∧
          ∃ G : (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 : Set (ℝ × ℝ)) ≃ₜ M i,
            G.IsFinitePL ∧
            (∀ x, (G x : E) ∈ d i ↔ (x : ℝ × ℝ).2 = 0) ∧
            (∀ x, (G x : E) ∈ d (n i) ↔ (x : ℝ × ℝ).2 = 1) ∧
            (∀ x, (G x : E) ∈ F '' (cornerMap (c i) '' ({0} ×ˢ Icc (b i) (b (n i)))) ↔
              (x : ℝ × ℝ).1 = 0) ∧
            (∀ x, (G x : E) ∈ F '' (cornerMap (c i) '' (Icc (a i) (a (n i)) ×ˢ {0})) ↔
              (x : ℝ × ℝ).1 = 1) := by
  classical
  obtain ⟨F,R,p,q,hRF,hFR,hface,hverts,hfront,hrestore,hD,hpq,hDsub,hDrim,hDdis,
    hpv,hqv,hleft,hbottom,hdiag⟩ :=
    exists_original_normal_family_coordinates K hs hs3 d r hd hsub hrim hdis hvertex hnr
  obtain ⟨c,a,b,ha,hb,htype,hcard,hbound,n,N,hNinj,hdata⟩ :=
    exists_distinct_successor_rectangle_family (fun i => R '' d i) p q hD hDsub hDrim hDdis
      hpv hqv hleft hbottom hdiag
  let Good := {i : ι // ∃ j, c j = c i ∧ a i < a j}
  let M : Good → Set E := fun i => F '' N i
  have hMinj : Function.Injective M := by
    intro i j he
    exact hNinj ((Set.image_injective.mpr hRF.injective) he)
  let T := base \ ⋃ i, R '' d i
  let U := convexHull ℝ (s : Set E) \ ⋃ i, d i
  have hFT : F '' T = U := by
    rw [image_sdiff hRF.injective,hface,image_iUnion]
    simp_rw [hrestore]
    rfl
  have hrcoords (i : ι) :
      r i = F '' (cornerMap (c i) '' ({(0,b i),(a i,0)} : Set (ℝ × ℝ))) := by
    have he : cornerMap (c i) '' ({(0,b i),(a i,0)} : Set (ℝ × ℝ)) = {p i,q i} := by
      rw [←htype i,image_image]
      have hf : (cornerMap (c i) ∘ cornerMap (c i)) = id :=
        funext (cornerMap_involutive (c i))
      change (cornerMap (c i) ∘ cornerMap (c i)) '' ({p i,q i} : Set (ℝ × ℝ)) = _
      rw [hf,image_id]
    rw [he,hDrim i,image_inter hRF.injective,hrestore i,hfront,←hrim i]
  refine ⟨F,R,c,a,b,hRF,hFR,hface,hverts,hfront,ha,hb,hrcoords,hcard,hbound,n,M,hMinj,?_⟩
  intro i
  obtain ⟨hnc,hlt,hN,hNB,hother,hcomp,G,hG,hGW,hGZ,hGL,hGR⟩ := hdata i
  have hmodel : IsFinitePLBallPair (ℝ × ℝ) (M i)
      (d i ∪ (d (n i) ∪ F '' (cornerMap (c i) '' edgeIntervals (a i) (b i) (a (n i)) (b (n i))))) := by
    have h := hN.affine_image F hRF.injective.injOn
    simpa only [image_union,hrestore] using h
  have havoid (k : ι) (hki : k ≠ (i : ι)) (hkn : k ≠ n i) : Disjoint (d k) (M i) := by
    rw [←hrestore k]
    exact (hother k hki hkn).image hRF.injective.injOn (subset_univ _) (subset_univ _)
  have hwhole : M i ∩ (⋃ k, d k) = d i ∪ d (n i) := by
    apply Subset.antisymm
    · rintro x ⟨hxM,hxd⟩
      obtain ⟨k,hxk⟩ := mem_iUnion.mp hxd
      by_cases hki : k = i
      · exact Or.inl (hki ▸ hxk)
      by_cases hkn : k = n i
      · exact Or.inr (hkn ▸ hxk)
      exact (disjoint_left.mp (havoid k hki hkn) hxk hxM).elim
    · intro x hx
      refine ⟨hmodel.1 ?_,?_⟩
      · rcases hx with hx | hx
        · exact Or.inl hx
        · exact Or.inr (Or.inl hx)
      · rcases hx with hx | hx
        · exact mem_iUnion.mpr ⟨i,hx⟩
        · exact mem_iUnion.mpr ⟨n i,hx⟩
  refine ⟨hnc,hlt,hmodel,?_,havoid,hwhole,?_,?_⟩
  · change (F '' N i) ∩ _ = _
    rw [←hfront,←image_inter hRF.injective,hNB]
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := hx.1
    have hy' : y ∈ N i \ ((R '' d i) ∪ (R '' d (n i))) := by
      refine ⟨hy,?_⟩
      rintro (hyD | hyD)
      · exact hx.2 (Or.inl ((hrestore i).subset (mem_image_of_mem F hyD)))
      · exact hx.2 (Or.inr ((hrestore (n i)).subset (mem_image_of_mem F hyD)))
    obtain ⟨hycomp,hyclosure⟩ := hcomp y hy'
    have hyT : y ∈ T := connectedComponentIn_subset _ _
      (hycomp.symm.subset hy')
    have hc := normalization_image_component F.continuous R.continuous hRF hyT
    have hcl := normalization_image_component_closure F.continuous R.continuous hRF hyT
      (hyclosure.symm ▸ hN.isCompact)
    rw [hFT,hycomp,image_sdiff hRF.injective,image_union,hrestore,hrestore] at hc
    rw [hFT,hyclosure] at hcl
    exact ⟨hc.symm,hcl⟩
  · obtain ⟨J,hJ,hJval⟩ := exists_affine_image_square_chart F hRF.injective G hG
    refine ⟨J,hJ,?_,?_,?_,?_⟩
    · intro x
      rw [hJval,←hrestore i,hRF.injective.mem_set_image]
      exact hGW x
    · intro x
      rw [hJval,←hrestore (n i),hRF.injective.mem_set_image]
      exact hGZ x
    · intro x
      rw [hJval,hRF.injective.mem_set_image]
      exact hGL x
    · intro x
      rw [hJval,hRF.injective.mem_set_image]
      exact hGR x

end PoincareConjecture.M76.PrismBelt
