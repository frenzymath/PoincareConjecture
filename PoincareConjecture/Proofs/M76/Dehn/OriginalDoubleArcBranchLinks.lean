import PoincareConjecture.Proofs.M76.Dehn.OriginalDoubleArcCrossedStar
import PoincareConjecture.Proofs.M76.Mathlib.SupportedFinitePLExtension
import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedImageReparameterization
import PoincareConjecture.Proofs.M76.Mathlib.ClosedStarInteriorBall
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderComplexityOrdinaryDiskBoundary












set_option autoImplicit false

open Set Geometry unitInterval

namespace PoincareConjecture.M76.Dehn

private theorem exists_link_polygon_of_affine_parameter
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {q : E → ℝ × ℝ} (hq : K.AffineOnFaces q) (hi : InjOn q K.space)
    {v : E} (hv : v ∈ K.vertices) (hint : q v ∈ interior (q '' K.space)) :
    ∃ (n : ℕ) (P : Polygon E (n + 3)), Function.Injective P ∧
      P.HasSimplicialEdges ∧ P.boundary ℝ = (K.link v).space := by
  classical
  let L := hq.embeddedImage hi
  have hL : L.faces.Finite := hq.embeddedImage_finite hi hK
  have hvL : q v ∈ L.vertices := by
    rw [hq.embeddedImage_vertices hi]
    exact ⟨v, hv, rfl⟩
  have hintL : q v ∈ interior L.space := by
    rw [hq.embeddedImage_space hi]
    exact hint
  have hball := L.isFinitePLBallPair_closedStar_of_interior hL hvL hintL
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm
  obtain ⟨n, P, hPi, hP, hPb⟩ := hball.exists_polygon_boundary
  let u := Function.invFunOn q K.space
  have hu : FinitePiecewiseAffineOn u L.space :=
    (hq.invFunOn_embeddedImage hi).finitePiecewiseAffineOn hL
  have hui : InjOn u L.space := by
    rw [hq.embeddedImage_space hi]
    exact Function.invFunOn_injOn_image q K.space
  have hsub : P.boundary ℝ ⊆ L.space := by
    rw [hPb]
    exact SimplicialComplex.space_subset_of_le
      (show L.link (q v) ≤ L from fun _ hs => hs.1)
  obtain ⟨m, Q, hQi, hQ, hQb⟩ :=
    P.exists_polygon_finitePL_image hP hPi hu hsub (hui.mono hsub)
  have hlink : (L.link (q v)).space = q '' (K.link v).space :=
    hq.embeddedImage_link_space hi hv
  have hlinksub : (K.link v).space ⊆ K.space :=
    SimplicialComplex.space_subset_of_le (show K.link v ≤ K from fun _ hs => hs.1)
  refine ⟨m, Q, hQi, hQ, ?_⟩
  rw [hQb, hPb, hlink]
  exact hi.invFunOn_image hlinksub








theorem exists_parameterized_protected_branch_repair
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E]
    (J P P₀ : SimplicialComplex ℝ E)
    (hJ : J.faces.Finite) (hP : P.faces.Finite) (hP₀ : P₀.faces.Finite)
    (hcv : Convex ℝ J.space) (hP₀P : P₀.space ⊆ P.space)
    (hPJ : P.space ⊆ J.space)
    (hfront : P.space ∩ frontier J.space ⊆ P₀.space)
    (q : E → ℝ × ℝ) (hq : FinitePiecewiseAffineOn q P.space)
    (hqi : InjOn q P.space)
    (ell : E →L[ℝ] ℝ) (hell : ell ≠ 0) :
    ∃ R K K₀ L : SimplicialComplex ℝ E,
      R.faces.Finite ∧ R.IsSubdivision J ∧ K ≤ R ∧ K.space = P.space ∧
      K.AffineOnFaces q ∧ K₀ ≤ K ∧ K₀.space = P₀.space ∧
      (∀ s ∈ K.faces, (∀ v ∈ s, v ∈ K₀.vertices) → s ∈ K₀.faces) ∧
      L.faces.Finite ∧ L.space = J.space ∩ {x | ell x = 0} ∧
      (∀ v ∈ K.vertices, q v ∈ interior (q '' P.space) →
        ∃ (n : ℕ) (Q : Polygon E (n + 3)), Function.Injective Q ∧
          Q.HasSimplicialEdges ∧ Q.boundary ℝ = (K.link v).space) ∧
      ∃ δ : ℝ, 0 < δ ∧
        (∀ v ∈ R.vertices, ell v ≠ 0 → δ ≤ |ell v|) ∧
        ∀ ε : ℝ, 0 < ε → ∃ H : PLCarrierMotion J.space P₀.space ε,
          R.AffineOnFaces (H.map 1) ∧
          (∀ v ∈ R.vertices, ell v ≠ 0 → ∀ t,
            |ell (H.map t v) - ell v| < |ell v| / 2 ∧
              (0 < ell (H.map t v) ↔ 0 < ell v) ∧
              (ell (H.map t v) < 0 ↔ ell v < 0)) ∧
          (∀ v ∈ K.vertices,
            ell (H.map 1 v) = 0 ↔ v ∈ K₀.vertices ∧ ell v = 0) ∧
          (∀ s ∈ K.faces, (∀ v ∈ s, ell (H.map 1 v) = 0) ↔
            s ∈ K₀.faces ∧ ∀ v ∈ s, ell v = 0) ∧
          (∀ s ∈ K.faces, s ∉ K₀.faces → ∀ t ∈ L.faces,
            affineSpan ℝ (H.map 1 '' (s : Set E) ∪ (t : Set E)) = ⊤ ∨
              Disjoint (intrinsicInterior ℝ (convexHull ℝ (H.map 1 '' (s : Set E))))
                (convexHull ℝ (t : Set E))) ∧
          ∃ B A : SimplicialComplex ℝ E,
            B.faces.Finite ∧ B.space = J.space ∧ A ≤ B ∧
            A.space = H.map 1 '' P.space ∧ K₀ ≤ A ∧
            A.AffineOnFaces (q ∘ (H.map 1).symm) ∧
            InjOn (q ∘ (H.map 1).symm) A.space ∧
            (∀ v ∈ K.vertices,
              (A.link (H.map 1 v)).space = H.map 1 '' (K.link v).space ∧
              (A.closedStar (H.map 1 v)).space = H.map 1 '' (K.closedStar v).space) ∧
            ∀ v ∈ K.vertices, q v ∈ interior (q '' P.space) →
              ∃ (n : ℕ) (Q : Polygon E (n + 3)), Function.Injective Q ∧
                Q.HasSimplicialEdges ∧ Q.boundary ℝ = (A.link (H.map 1 v)).space := by
  classical
  obtain ⟨u, ⟨T, hT, hTJ, huT⟩, huq, _, _⟩ :=
    hq.exists_supported_extension J hJ hPJ isOpen_univ (subset_univ _)
  obtain ⟨N, hN, hNJ, hNT⟩ := J.exists_common_finite_subdivision T hJ hT hTJ.symm
  have huN : N.AffineOnFaces u := hNT.affineOnFaces huT
  have hNs : N.space = J.space := hNJ.space_eq
  have hrepair := exists_protected_branch_repair N P P₀ hN hP hP₀
    (hNs.symm ▸ hcv) hP₀P (fun x hx => hNs.symm.subset (hPJ hx))
    (by simpa only [hNs] using hfront) ell hell
  rw [hNs] at hrepair
  obtain ⟨R, K, K₀, L, hR, hRN, hKR, hKs, hK₀K, hK₀s, hfull,
    hL, hLs, δ, hδ, hmargin, hmotions⟩ := hrepair
  have hK : K.faces.Finite := hR.subset hKR
  have hqK : K.AffineOnFaces q :=
    (show K.AffineOnFaces u from fun s hs =>
      (hRN.affineOnFaces huN) s (hKR hs)).congr
        (fun x hx => huq (hKs.subset hx))
  have hqiK : InjOn q K.space := hqi.mono hKs.subset
  have hlinks (v : E) (hv : v ∈ K.vertices)
      (hvint : q v ∈ interior (q '' P.space)) :
      ∃ (n : ℕ) (Q : Polygon E (n + 3)), Function.Injective Q ∧
        Q.HasSimplicialEdges ∧ Q.boundary ℝ = (K.link v).space :=
    exists_link_polygon_of_affine_parameter K hK hqK hqiK hv (by rwa [hKs])
  refine ⟨R, K, K₀, L, hR, hRN.trans hNJ, hKR, hKs, hqK, hK₀K,
    hK₀s, hfull, hL, hLs, hlinks, δ, hδ, hmargin, ?_⟩
  intro ε hε
  obtain ⟨H, hH, hsigns, hzeros, hfaces, _, hposition⟩ := hmotions ε hε
  have hHK : K.AffineOnFaces (H.map 1) := fun s hs => hH s (hKR hs)
  have hHiR : InjOn (H.map 1) R.space := (H.map 1).injective.injOn
  have hHiK : InjOn (H.map 1) K.space := (H.map 1).injective.injOn
  let B := hH.embeddedImage hHiR
  let A := hHK.embeddedImage hHiK
  have hB : B.faces.Finite := hH.embeddedImage_finite hHiR hR
  have hBs : B.space = J.space := by
    rw [hH.embeddedImage_space hHiR, (hRN.trans hNJ).space_eq, H.carrier 1]
  have hAB : A ≤ B := by
    intro s hs
    change s ∈ (hHK.embeddedImage hHiK).faces at hs
    change s ∈ (hH.embeddedImage hHiR).faces
    rw [hHK.embeddedImage_faces hHiK] at hs
    rw [hH.embeddedImage_faces hHiR]
    obtain ⟨t, ht, rfl⟩ := hs
    exact ⟨t, hKR ht, rfl⟩
  have hAs : A.space = H.map 1 '' P.space := by
    rw [hHK.embeddedImage_space hHiK, hKs]
  have hprotected : K₀ ≤ A := hHK.protected_le_embeddedImage hHiK hK₀K
    (fun x hx => H.fixed_protected 1 x (hK₀s.subset hx))
  have hleft : LeftInvOn (H.map 1).symm (H.map 1) K.space :=
    fun x _ => (H.map 1).symm_apply_apply x
  have hparam : A.AffineOnFaces (q ∘ (H.map 1).symm) :=
    hHK.comp_inverse_on_embeddedImage hqK hHiK hleft
  have hparami : InjOn (q ∘ (H.map 1).symm) A.space :=
    hHK.injOn_comp_inverse_on_embeddedImage hHiK hqiK hleft
  have hparameterImage : (q ∘ (H.map 1).symm) '' A.space = q '' P.space := by
    rw [hAs, image_image]
    congr 1
    funext x
    exact congrArg q ((H.map 1).symm_apply_apply x)
  refine ⟨H, hH, hsigns, hzeros, hfaces, hposition, B, A,
    hB, hBs, hAB, hAs, hprotected, hparam, hparami, ?_, ?_⟩
  · intro v hv
    exact ⟨hHK.embeddedImage_link_space hHiK hv,
      hHK.embeddedImage_closedStar_space hHiK hv⟩
  · intro v hv hvint
    have hvA : H.map 1 v ∈ A.vertices := by
      rw [hHK.embeddedImage_vertices hHiK]
      exact ⟨v, hv, rfl⟩
    apply exists_link_polygon_of_affine_parameter A (hB.subset hAB) hparam hparami hvA
    change q ((H.map 1).symm (H.map 1 v)) ∈ interior ((q ∘ (H.map 1).symm) '' A.space)
    rw [(H.map 1).symm_apply_apply, hparameterImage]
    exact hvint

end PoincareConjecture.M76.Dehn
