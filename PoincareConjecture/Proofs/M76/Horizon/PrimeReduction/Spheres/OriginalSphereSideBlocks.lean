import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.OriginalSphereSideStars
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Regions.SphereSideDualHalfBall
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Simplicial.FlatSphereIncidence

set_option autoImplicit false
set_option maxHeartbeats 1400000

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem ChartwisePLSphere.exists_original_side_blocks
    {X ι : Type*} [MetricSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R S : Set X}
    (s : ChartwisePLSphere e S) (hR : IsCompact R) (he : PLDomain e R)
    (hSR : S ⊆ interior R) :
    ∃ (t : Finset R) (F : X → (t → ℝ × V3))
      (K L N T P M : SimplicialComplex ℝ (t → ℝ × V3))
      (H : R ≃ₜ K.space) (g : (t → ℝ × V3) → R)
      (W Rpos Rneg : Set X)
      (B : N.vertices → OpenPartialHomeomorph X V3)
      (hK : K.faces.Finite) (_hT : T.faces.Finite)
      (hP : P.faces.Finite) (hM : M.faces.Finite) (hN : N.faces.Finite),
      let : Fintype K.faces := hK.fintype
      let : Fintype P.faces := hP.fintype
      let : Fintype M.faces := hM.fintype
      let : Fintype N.faces := hN.fintype
      Continuous F ∧
      (∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target) ∧
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
      (∀ a ∈ N.faces, ∃ b ∈ N.faces, a ⊆ b ∧ b.card = 3) ∧
      (∀ a ∈ N.faces, a.card = 2 → (N.faceLink a).vertices.ncard = 2) ∧
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
        IsFinitePLBallPair (ℝ × ℝ) (N.closedStar p).space (N.link p).space ∧
        Nonempty (SimplicialComplex.BoundaryVertexHalfBall P N p) ∧
        Nonempty (SimplicialComplex.BoundaryVertexHalfBall M N p) := by
  classical
  obtain ⟨t, F, K, L, N, T, P, M, H, g, W, Rp, Rn, B,
    hFc, hF, hK, hT, hP, hM, hLK, hTK, hNT, hPT, hMT, hNP, hNM,
    hLf, hNf, hPf, hMf, hNfull, hKs, hLs, hNs, hHF, hgc, hg, hgPL,
    hW, hSW, hu, hi, hTf, hTs, hTW, hPs, hMs, hPMu, hPMi, hfaces, hinter, hstars⟩ :=
    s.exists_original_side_star_halfballs hR he hSR
  have hNK : N ≤ K := fun _ ha => hTK (hNT ha)
  have hPK : P ≤ K := fun _ ha => hTK (hPT ha)
  have hMK : M ≤ K := fun _ ha => hTK (hMT ha)
  have hN : N.faces.Finite := hK.subset hNK
  let : Fintype K.faces := hK.fintype
  let : Fintype P.faces := hP.fintype
  let : Fintype M.faces := hM.fintype
  let : Fintype N.faces := hN.fintype
  have hflat : ∀ p : N.vertices, ∃ f : (t → ℝ × V3) → V3,
      (K.closedStar p).AffineOnFaces f ∧ InjOn f (K.closedStar p).space ∧
      f p ∈ interior (f '' (K.closedStar p).space) ∧
      ∀ z ∈ (K.closedStar p).space, z ∈ N.space ↔ f z 0 = 0 := by
    intro p
    obtain ⟨_, _, _, hf, hinj, _, hint, hmodel, _⟩ := hstars p
    exact ⟨fun z => B p (g z), hf, hinj, hint, fun z hz => (hmodel z hz).1⟩
  obtain ⟨hpure, hedge⟩ := K.surface_incidence_of_flat_ambient_stars N hK hNK hNf hflat
  refine ⟨t, F, K, L, N, T, P, M, H, g, W, Rp, Rn, B, hK, hT, hP, hM, hN,
    hFc, hF, hLK, hTK, hNT, hPT, hMT, hNP, hNM,
    hLf, hNf, hPf, hMf, hNfull, hKs, hLs, hNs, hHF, hgc, hg, hgPL,
    hW, hSW, hu, hi, hTf, hTs, hTW, hPs, hMs, hPMu, hPMi, hfaces, hinter,
    hpure, hedge, ?_⟩
  intro p
  obtain ⟨hsource, hBW, hB, hf, hinj, hO, hint, hmodel, hTstar, hTlink,
    hPstar, hMstar, hNstar, hPlink, hMlink, hNlink, hposball, hnegball, hdisk⟩ := hstars p
  have hpK : (p : t → ℝ × V3) ∈ K.vertices := hNK p.property
  have hpstar : (p : t → ℝ × V3) ∈ (K.closedStar p).space := by
    apply (K.closedStar p).vertices_subset_space
    refine ⟨hpK, ?_⟩
    rw [Finset.insert_eq_of_mem (Finset.mem_singleton_self _)]
    exact hpK
  have hzero : (B p (g p)) 0 = 0 :=
    (hmodel p hpstar).1.mp (N.vertices_subset_space p.property)
  have hpos := K.exists_sphere_side_dual_half_ball P N hPK hNP p.property hf hinj
    hzero hint hPstar (fun z hz => (hmodel z hz).1)
  let a : V3 ≃L[ℝ] V3 := ContinuousLinearEquiv.neg ℝ
  let f : (t → ℝ × V3) → V3 := fun z => a (B p (g z))
  have hfneg : (K.closedStar p).AffineOnFaces f :=
    hf.postcomp a.toContinuousAffineEquiv.toContinuousAffineMap
  have hnegInj : InjOn f (K.closedStar p).space := fun _ hx _ hy h =>
    hinj hx hy (a.injective h)
  have hnegZero : f p 0 = 0 := by
    change -((B p (g p)) 0) = 0
    rw [hzero, neg_zero]
  have hnegInt : f p ∈ interior (f '' (K.closedStar p).space) := by
    change a (B p (g p)) ∈ interior ((a ∘ (fun z => B p (g z))) '' (K.closedStar p).space)
    rw [image_comp]
    change a.toHomeomorph (B p (g p)) ∈
      interior (a.toHomeomorph '' ((fun z => B p (g z)) '' (K.closedStar p).space))
    rw [← a.toHomeomorph.image_interior]
    exact mem_image_of_mem _ hint
  have hnegSide : (M.closedStar p).space = (K.closedStar p).space ∩ {z | 0 ≤ f z 0} := by
    change (M.closedStar p).space = (K.closedStar p).space ∩ {z | 0 ≤ -((B p (g z)) 0)}
    simpa only [neg_nonneg] using hMstar
  have hnegBoundary (z : t → ℝ × V3) (hz : z ∈ (K.closedStar p).space) :
      z ∈ N.space ↔ f z 0 = 0 := by
    change z ∈ N.space ↔ -((B p (g z)) 0) = 0
    simpa only [neg_eq_zero] using (hmodel z hz).1
  have hneg := K.exists_sphere_side_dual_half_ball M N hMK hNM p.property
    hfneg hnegInj hnegZero hnegInt hnegSide hnegBoundary
  exact ⟨hsource, hBW, hB, hf, hinj, hO, hint, hmodel, hTstar, hTlink,
    hPstar, hMstar, hNstar, hPlink, hMlink, hNlink,
    hposball, hnegball, hdisk, hpos, hneg⟩

end PoincareConjecture.M76
