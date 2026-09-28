import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.OriginalSphereDomainStars
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Simplicial.ClosedSideSubcomplexes
import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Simplicial.CommonSubcomplexUnion











set_option autoImplicit false
set_option maxHeartbeats 1200000

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]



theorem exists_closed_side_star_partition
    (K N : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hNK : N ≤ K)
    (g : E → X) (hgc : ContinuousOn g K.space)
    {W Rp Rn S : Set X}
    (hpc : IsClosed ((Subtype.val : W → X) ⁻¹' Rp))
    (hnc : IsClosed ((Subtype.val : W → X) ⁻¹' Rn))
    (hu : Rp ∪ Rn = W) (hi : Rp ∩ Rn = S)
    (hmem : ∀ z ∈ K.space, g z ∈ S ↔ z ∈ N.space)
    (hstar : ∀ p : N.vertices, MapsTo g (K.closedStar p).space W) :
    ∃ T P M : SimplicialComplex ℝ E,
      T ≤ K ∧ N ≤ T ∧ P ≤ T ∧ M ≤ T ∧ N ≤ P ∧ N ≤ M ∧
      T.faces.Finite ∧ P.faces.Finite ∧ M.faces.Finite ∧
      T.faces = ⋃ p : N.vertices, (K.closedStar p).faces ∧
      T.space = ⋃ p : N.vertices, (K.closedStar p).space ∧
      MapsTo g T.space W ∧
      P.space = T.space ∩ g ⁻¹' Rp ∧ M.space = T.space ∩ g ⁻¹' Rn ∧
      P.space ∪ M.space = T.space ∧ P.space ∩ M.space = N.space ∧
      (∀ a ∈ T.faces, a ∈ P.faces ∨ a ∈ M.faces) ∧
      P.faces ∩ M.faces = N.faces := by
  classical
  let C (p : N.vertices) := K.closedStar p
  have hCK (p : N.vertices) : C p ≤ K := fun _ ha => ha.1
  have hcross : ∀ i j : N.vertices, ∀ a ∈ (C i).faces, ∀ b ∈ (C j).faces,
      convexHull ℝ (a : Set E) ∩ convexHull ℝ (b : Set E) ⊆
        convexHull ℝ ((a : Set E) ∩ b) :=
    fun i j _ ha _ hb => K.inter_subset_convexHull (hCK i ha) (hCK j hb)
  let T := iUnionOfCompatible C hcross
  have hCT (p : N.vertices) : C p ≤ T := le_iUnionOfCompatible C hcross p
  have hTK : T ≤ K := by
    intro a ha
    obtain ⟨p, hp⟩ := mem_iUnion.mp ha
    exact hCK p hp
  have hNT : N ≤ T := by
    intro a ha
    obtain ⟨p, hp⟩ := N.nonempty_of_mem_faces ha
    let pN : N.vertices := ⟨p, N.face_subset_vertices ha hp⟩
    apply hCT pN
    refine ⟨hNK ha, ?_⟩
    change insert p a ∈ K.faces
    simpa only [Finset.insert_eq_of_mem hp] using hNK ha
  have hT : T.faces.Finite := hK.subset hTK
  have hTs : T.space = ⋃ p : N.vertices, (K.closedStar p).space :=
    space_iUnionOfCompatible C hcross
  have hTW : MapsTo g T.space W := by
    intro z hz
    obtain ⟨p, hp⟩ := mem_iUnion.mp (hTs.subset hz)
    exact hstar p hp
  let f : T.space → W := fun z => ⟨g z, hTW z.property⟩
  have hf : Continuous f :=
    (hgc.mono (space_subset_of_le hTK)).domRestrict.subtype_mk _
  let : CompactSpace T.space := isCompact_iff_compactSpace.mp (T.isCompact_space_of_finite hT)
  have hclosed (Q : Set X) (hQ : IsClosed ((Subtype.val : W → X) ⁻¹' Q)) :
      IsClosed (T.space ∩ g ⁻¹' Q) := by
    have heq : T.space ∩ g ⁻¹' Q =
        (Subtype.val : T.space → E) '' (f ⁻¹' ((Subtype.val : W → X) ⁻¹' Q)) := by
      ext z
      constructor
      · intro hz
        exact ⟨⟨z, hz.1⟩, hz.2, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z.property, hz⟩
    rw [heq]
    exact ((hQ.preimage hf).isCompact.image continuous_subtype_val).isClosed
  have hpu : (T.space ∩ g ⁻¹' Rp) ∪ (T.space ∩ g ⁻¹' Rn) = T.space := by
    ext z
    constructor
    · exact fun hz => hz.elim And.left And.left
    · intro hz
      exact (hu.symm.subset (hTW hz)).elim (fun hp => Or.inl ⟨hz, hp⟩)
        (fun hn => Or.inr ⟨hz, hn⟩)
  have hpi : (T.space ∩ g ⁻¹' Rp) ∩ (T.space ∩ g ⁻¹' Rn) = N.space := by
    ext z
    constructor
    · intro hz
      exact (hmem z (space_subset_of_le hTK hz.1.1)).mp (hi.subset ⟨hz.1.2, hz.2.2⟩)
    · intro hz
      have hzT := space_subset_of_le hNT hz
      have hzS := (hmem z (space_subset_of_le hTK hzT)).mpr hz
      have hzn := hi.symm.subset hzS
      exact ⟨⟨hzT, hzn.1⟩, hzT, hzn.2⟩
  obtain ⟨P, M, hPT, hMT, hNP, hNM, hP, hM, hPs, hMs, hfaces, hinter⟩ :=
    T.exists_closed_side_subcomplexes N hT hNT (hclosed Rp hpc) (hclosed Rn hnc) hpu hpi
  exact ⟨T, P, M, hTK, hNT, hPT, hMT, hNP, hNM, hT, hP, hM, rfl, hTs, hTW,
    hPs, hMs, by rw [hPs, hMs]; exact hpu,
    by rw [hPs, hMs]; exact hpi, hfaces, hinter⟩

end Geometry.SimplicialComplex

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)





theorem ChartwisePLSphere.exists_original_side_subcomplexes
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
      L ≤ K ∧ T ≤ K ∧ N ≤ T ∧
      P ≤ T ∧ M ≤ T ∧ N ≤ P ∧ N ≤ M ∧
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
        ∀ z ∈ (K.closedStar p).space,
          (z ∈ N.space ↔ (B p (g z)) 0 = 0) ∧
          ((g z : X) ∈ Rpos ↔ 0 ≤ (B p (g z)) 0) ∧
          ((g z : X) ∈ Rneg ↔ (B p (g z)) 0 ≤ 0) := by
  classical
  obtain ⟨t, F, K, L, N, H, g, W, Rp, Rn, B, hFc, hF, hK, hLK, hNK,
    hLf, hNf, hKs, hLs, hNs, hHF, hgc, hg, hgPL,
    hW, hSW, hu, hi, hpc, hnc, hstars, _⟩ :=
    s.exists_oriented_domain_stars hR he hSR
  have hFinj : InjOn F R := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (H.injective (Subtype.ext
      ((hHF ⟨x, hx⟩).trans (hxy.trans (hHF ⟨y, hy⟩).symm))))
  have hFg (z : t → ℝ × V3) (hz : z ∈ K.space) : F (g z) = z := by
    rw [hg ⟨z, hz⟩]
    exact (hHF (H.symm ⟨z, hz⟩)).symm.trans
      (congrArg Subtype.val (H.apply_symm_apply ⟨z, hz⟩))
  have hmem (z : t → ℝ × V3) (hz : z ∈ K.space) :
      (g z : X) ∈ S ↔ z ∈ N.space := by
    rw [hNs]
    constructor
    · exact fun h => ⟨g z, h, hFg z hz⟩
    · rintro ⟨y, hy, hyz⟩
      exact hFinj (interior_subset (hSR hy)) (g z).property
        (hyz.trans (hFg z hz).symm) ▸ hy
  obtain ⟨T, P, M, hTK, hNT, hPT, hMT, hNP, hNM, hT, hP, hM,
    hTf, hTs, hTW, hPs, hMs, hPMu, hPMi, hfaces, hinter⟩ :=
    K.exists_closed_side_star_partition N hK hNK (fun z => (g z : X))
      (continuous_subtype_val.comp_continuousOn hgc) hpc hnc hu hi hmem
      (fun p z hz => (hstars p).2.1 ((hstars p).1 hz))
  have hNfT : ∀ a ∈ T.faces, (∀ v ∈ a, v ∈ N.vertices) → a ∈ N.faces :=
    fun a ha => hNf a (hTK ha)
  have hPf := T.full_of_closed_side_partition N P M hNP hNfT hfaces hinter
  have hMf := T.full_of_closed_side_partition N M P hNM hNfT
    (fun a ha => (hfaces a ha).symm) ((inter_comm M.faces P.faces).trans hinter)
  refine ⟨t, F, K, L, N, T, P, M, H, g, W, Rp, Rn, B,
    hFc, hF, hK, hT, hP, hM, hLK, hTK, hNT, hPT, hMT, hNP, hNM, hLf, hNf, hPf, hMf,
    ?_, hKs, hLs, hNs, hHF, hgc, hg, hgPL, hW, hSW, hu, hi,
    hTf, hTs, hTW, hPs, hMs, hPMu, hPMi, hfaces, hinter, hstars⟩
  intro Q hQ a ha hv
  rcases hQ with rfl | rfl | hQ
  · exact hNfT a ha hv
  · exact hNfT a (hPT ha) hv
  · have hQM : Q = M := hQ
    subst Q
    exact hNfT a (hMT ha) hv

end PoincareConjecture.M76
