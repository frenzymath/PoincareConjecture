import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.OriginalSphereSideSubcomplexes
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Simplicial.FullSubcomplexStars
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Regions.VertexStarHalfBalls
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Regions.VertexStarZeroDisk










set_option autoImplicit false
set_option maxHeartbeats 1200000

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

omit [FiniteDimensional ℝ E] in
private theorem star_link_eq_region_of_full
    (K T Q : SimplicialComplex ℝ E) (hT : T.faces.Finite) (hTK : T ≤ K)
    (hQT : Q ≤ T)
    (hfull : ∀ a ∈ T.faces, (∀ v ∈ a, v ∈ Q.vertices) → a ∈ Q.faces)
    {p : E} (hp : p ∈ Q.vertices) (hstar : K.closedStar p ≤ T)
    {D : Set E} (hmem : ∀ z ∈ (K.closedStar p).space, z ∈ Q.space ↔ z ∈ D) :
    (Q.closedStar p).space = (K.closedStar p).space ∩ D ∧
      (Q.link p).space = (K.link p).space ∩ D := by
  have hs := K.closedStar_eq_of_retains_closedStar T hTK p hstar
  have hl := K.link_eq_of_retains_closedStar T hTK p hstar
  have hqs := T.closedStar_space_eq_inter_of_full Q hT hQT hfull hp
  have hql := T.link_space_eq_inter_of_full Q hT hQT hfull hp
  rw [hs] at hqs
  rw [hl] at hql
  constructor
  · rw [hqs]
    ext z
    exact and_congr_right (hmem z)
  · rw [hql]
    ext z
    exact and_congr_right (fun hz => hmem z
      (space_subset_of_le (K.link_le_closedStar p) hz))

end Geometry.SimplicialComplex

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)




theorem ChartwisePLSphere.exists_original_side_star_halfballs
    {X ι : Type*} [MetricSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R S : Set X}
    (s : ChartwisePLSphere e S) (hR : IsCompact R) (he : PLDomain e R)
    (hSR : S ⊆ interior R) :
    ∃ (t : Finset R) (F : X → (t → ℝ × V3))
      (K L N T P M : SimplicialComplex ℝ (t → ℝ × V3))
      (H : R ≃ₜ K.space) (g : (t → ℝ × V3) → R)
      (W Rpos Rneg : Set X)
      (B : N.vertices → OpenPartialHomeomorph X V3),
      Continuous F ∧
      (∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target) ∧
      K.faces.Finite ∧ T.faces.Finite ∧ P.faces.Finite ∧ M.faces.Finite ∧
      L ≤ K ∧ T ≤ K ∧ N ≤ T ∧ P ≤ T ∧ M ≤ T ∧ N ≤ P ∧ N ≤ M ∧
      (∀ a ∈ K.faces, (∀ v ∈ a, v ∈ L.vertices) → a ∈ L.faces) ∧
      (∀ a ∈ K.faces, (∀ v ∈ a, v ∈ N.vertices) → a ∈ N.faces) ∧
      (∀ a ∈ T.faces, (∀ v ∈ a, v ∈ P.vertices) → a ∈ P.faces) ∧
      (∀ a ∈ T.faces, (∀ v ∈ a, v ∈ M.vertices) → a ∈ M.faces) ∧
      (∀ Q ∈ ({T, P, M} : Set (SimplicialComplex ℝ (t → ℝ × V3))),
        ∀ a ∈ Q.faces, (∀ v ∈ a, v ∈ N.vertices) → a ∈ N.faces) ∧
      K.space = F '' R ∧ L.space = F '' frontier R ∧ N.space = F '' S ∧
      (∀ x : R, (H x : t → ℝ × V3) = F x) ∧
      ContinuousOn g K.space ∧
      (∀ z : K.space, (g z : X) = (H.symm z : X)) ∧
      PolyhedralPLInCharts e (fun z => (g z : X)) K.space ∧
      IsOpen W ∧ S ⊆ W ∧ Rpos ∪ Rneg = W ∧ Rpos ∩ Rneg = S ∧
      T.faces = ⋃ p : N.vertices, (K.closedStar p).faces ∧
      T.space = ⋃ p : N.vertices, (K.closedStar p).space ∧
      MapsTo (fun z => (g z : X)) T.space W ∧
      P.space = T.space ∩ (fun z => (g z : X)) ⁻¹' Rpos ∧
      M.space = T.space ∩ (fun z => (g z : X)) ⁻¹' Rneg ∧
      P.space ∪ M.space = T.space ∧ P.space ∩ M.space = N.space ∧
      (∀ a ∈ T.faces, a ∈ P.faces ∨ a ∈ M.faces) ∧
      P.faces ∩ M.faces = N.faces ∧
      ∀ p : N.vertices,
        MapsTo (fun z => (g z : X)) (K.closedStar p).space (B p).source ∧
        (B p).source ⊆ W ∧
        (∀ i, (e i).symm.trans (B p) ∈ piecewiseAffineGroupoid V3) ∧
        (K.closedStar p).AffineOnFaces (fun z => B p (g z)) ∧
        InjOn (fun z => B p (g z)) (K.closedStar p).space ∧
        (∃ O : Set X, IsOpen O ∧ (g p : X) ∈ O ∧ O ⊆ (B p).source ∧
          O ⊆ (fun z => (g z : X)) '' (K.closedStar p).space) ∧
        B p (g p) ∈ interior ((fun z => B p (g z)) '' (K.closedStar p).space) ∧
        (∀ z ∈ (K.closedStar p).space,
          (z ∈ N.space ↔ (B p (g z)) 0 = 0) ∧
          ((g z : X) ∈ Rpos ↔ 0 ≤ (B p (g z)) 0) ∧
          ((g z : X) ∈ Rneg ↔ (B p (g z)) 0 ≤ 0)) ∧
        T.closedStar p = K.closedStar p ∧ T.link p = K.link p ∧
        (P.closedStar p).space = (K.closedStar p).space ∩ {z | 0 ≤ (B p (g z)) 0} ∧
        (M.closedStar p).space = (K.closedStar p).space ∩ {z | (B p (g z)) 0 ≤ 0} ∧
        (N.closedStar p).space = (K.closedStar p).space ∩ {z | (B p (g z)) 0 = 0} ∧
        (P.link p).space = (K.link p).space ∩ {z | 0 ≤ (B p (g z)) 0} ∧
        (M.link p).space = (K.link p).space ∩ {z | (B p (g z)) 0 ≤ 0} ∧
        (N.link p).space = (K.link p).space ∩ {z | (B p (g z)) 0 = 0} ∧
        IsFinitePLBallPair V3 (P.closedStar p).space
          ((P.link p).space ∪ (N.closedStar p).space) ∧
        IsFinitePLBallPair V3 (M.closedStar p).space
          ((M.link p).space ∪ (N.closedStar p).space) ∧
        IsFinitePLBallPair (ℝ × ℝ) (N.closedStar p).space (N.link p).space := by
  classical
  obtain ⟨t, F, K, L, N, T, P, M, H, g, W, Rp, Rn, B,
    hFc, hF, hK, hT, hP, hM, hLK, hTK, hNT, hPT, hMT, hNP, hNM,
    hLf, hNf, hPf, hMf, hNfull, hKs, hLs, hNs, hHF, hgc, hg, hgPL,
    hW, hSW, hu, hi, hTf, hTs, hTW, hPs, hMs, hPMu, hPMi, hfaces, hinter, hstars⟩ :=
    s.exists_original_side_subcomplexes hR he hSR
  refine ⟨t, F, K, L, N, T, P, M, H, g, W, Rp, Rn, B,
    hFc, hF, hK, hT, hP, hM, hLK, hTK, hNT, hPT, hMT, hNP, hNM,
    hLf, hNf, hPf, hMf, hNfull, hKs, hLs, hNs, hHF, hgc, hg, hgPL,
    hW, hSW, hu, hi, hTf, hTs, hTW, hPs, hMs, hPMu, hPMi, hfaces, hinter, ?_⟩
  intro p
  obtain ⟨hsource, hBW, hB, hf, hinj, hO, hint, hmodel⟩ := hstars p
  have hstar : K.closedStar (p : t → ℝ × V3) ≤ T := by
    intro a ha
    change a ∈ T.faces
    rw [hTf]
    exact mem_iUnion.mpr ⟨p, ha⟩
  have hstarT := SimplicialComplex.space_subset_of_le hstar
  have hpK : (p : t → ℝ × V3) ∈ K.vertices := hTK (hNT p.property)
  have hpstar : (p : t → ℝ × V3) ∈ (K.closedStar p).space := by
    apply (K.closedStar p).vertices_subset_space
    refine ⟨hpK, ?_⟩
    rw [Finset.insert_eq_of_mem (Finset.mem_singleton_self _)]
    exact hpK
  have hzero : (B p (g p)) 0 = 0 :=
    (hmodel p hpstar).1.mp (N.vertices_subset_space p.property)
  have hPmem (z : t → ℝ × V3) (hz : z ∈ (K.closedStar p).space) :
      z ∈ P.space ↔ 0 ≤ (B p (g z)) 0 := by
    rw [hPs]
    exact ⟨fun h => (hmodel z hz).2.1.mp h.2,
      fun h => ⟨hstarT hz, (hmodel z hz).2.1.mpr h⟩⟩
  have hMmem (z : t → ℝ × V3) (hz : z ∈ (K.closedStar p).space) :
      z ∈ M.space ↔ (B p (g z)) 0 ≤ 0 := by
    rw [hMs]
    exact ⟨fun h => (hmodel z hz).2.2.mp h.2,
      fun h => ⟨hstarT hz, (hmodel z hz).2.2.mpr h⟩⟩
  obtain ⟨hPstar, hPlink⟩ := K.star_link_eq_region_of_full T P hT hTK hPT hPf
    (hNP p.property) hstar (D := {z | 0 ≤ (B p (g z)) 0}) hPmem
  obtain ⟨hMstar, hMlink⟩ := K.star_link_eq_region_of_full T M hT hTK hMT hMf
    (hNM p.property) hstar (D := {z | (B p (g z)) 0 ≤ 0}) hMmem
  obtain ⟨hNstar, hNlink⟩ := K.star_link_eq_region_of_full T N hT hTK hNT
    (fun a ha => hNf a (hTK ha)) p.property hstar
    (D := {z | (B p (g z)) 0 = 0}) (fun z hz => (hmodel z hz).1)
  obtain ⟨hpos, hneg⟩ := K.isFinitePLBallPair_closedStar_chart_halfspaces hK hpK hf hinj hzero hint
  have hdisk := K.isFinitePLBallPair_closedStar_chart_zero_section hK hpK hf hinj hzero hint
  rw [← hPstar, ← hPlink, ← hNstar] at hpos
  rw [← hMstar, ← hMlink, ← hNstar] at hneg
  rw [← hNstar, ← hNlink] at hdisk
  exact ⟨hsource, hBW, hB, hf, hinj, hO, hint, hmodel,
    K.closedStar_eq_of_retains_closedStar T hTK p hstar,
    K.link_eq_of_retains_closedStar T hTK p hstar,
    hPstar, hMstar, hNstar, hPlink, hMlink, hNlink, hpos, hneg, hdisk⟩

end PoincareConjecture.M76
