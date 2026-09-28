import PoincareConjecture.Proofs.M76.Mathlib.CarrierChartInterior
import PoincareConjecture.Proofs.M76.Mathlib.ClosedStarCarrierNeighborhood
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallPairs
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLProduct
import PoincareConjecture.Proofs.M76.Mathlib.SupportedFinitePLExtension












set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]






theorem exists_faceAffine_vertex_stars_of_finite_ball_cover
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {ι : Type*} [Finite ι] (d q : ι → Set E)
    (hball : ∀ i, IsFinitePLBallPair F (d i) (q i))
    (hsub : ∀ i, d i ⊆ K.space)
    (hopen : ∀ i, IsOpen ((Subtype.val : K.space → E) ⁻¹' (d i \ q i)))
    (hcover : ∀ x : K.space, ∃ i, (x : E) ∈ d i \ q i)
    (A : E →ᵃ[ℝ] ℝ) :
    ∃ L : SimplicialComplex ℝ E, L.faces.Finite ∧ L.IsSubdivision K ∧
      L.RespectsAffineHyperplane A ∧
      ∀ p : E, {p} ∈ L.faces → ∃ f : E → F,
        (L.closedFaceStar {p}).AffineOnFaces f ∧
        InjOn f (L.closedFaceStar {p}).space ∧
        f p ∈ interior (f '' (L.closedFaceStar {p}).space) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  choose C hC hcv hne e he hboundary using fun i => (hball i).2
  choose f hf heval using he
  choose g hg hgf _ _ using fun i =>
    (hf i).exists_supported_extension K hK (hsub i) isOpen_univ (subset_univ _)
  obtain ⟨R, hR, hRK, hgR⟩ := FinitePiecewiseAffineOn.pi_on_complex K hK hg
  obtain ⟨T, hT, hTK, hTR⟩ :=
    K.exists_common_finite_subdivision R hK hR hRK.symm
  have hgT (i : ι) : T.AffineOnFaces (g i) :=
    (hTR.affineOnFaces hgR).postcomp
      (ContinuousLinearMap.proj i : (ι → F) →L[ℝ] F).toContinuousAffineMap
  let N := hT.toFinset.sup Finset.card
  have hN (s : Finset E) (hs : s ∈ T.faces) : s.card ≤ N + 1 :=
    (Finset.le_sup (hT.mem_toFinset.mpr hs)).trans (Nat.le_succ N)
  obtain ⟨D, hD, hDT, _, hDA⟩ := T.exists_subdivision_respectsAffineHyperplane hT hN A
  have hDK : D.IsSubdivision K := hDT.trans hTK
  let U : ι → Set D.space := fun i => Subtype.val ⁻¹' (d i \ q i)
  have hU (i : ι) : IsOpen (U i) :=
    (hopen i).preimage (Homeomorph.setCongr hDK.space_eq).continuous
  have hUcover (x : D.space) : ∃ i, x ∈ U i :=
    hcover ⟨x, hDK.space_eq.subset x.property⟩
  obtain ⟨L, hL, hLD, hstars⟩ := D.exists_finite_subdivision_stars hD U hU hUcover
  have hLK := hLD.trans hDK
  refine ⟨L, hL, hLK, hLD.respectsAffineHyperplane hDA, ?_⟩
  intro p hp
  obtain ⟨i, hi⟩ := hstars p hp
  let S := (L.closedFaceStar {p}).space
  have hSL : S ⊆ L.space := space_subset_of_le (fun _ ht => ht.1)
  have hSdq : S ⊆ d i \ q i := by
    intro x hx
    exact hi ⟨x, hLD.space_eq.subset (hSL hx)⟩ hx
  have hpL : p ∈ L.space := L.convexHull_subset_space hp (by simp)
  have hnS : (Subtype.val ⁻¹' S : Set L.space) ∈ 𝓝 (⟨p, hpL⟩ : L.space) :=
    L.closedFaceStar_mem_nhds_of_intrinsicInterior hL hp ⟨p, hpL⟩ (by
      simp [intrinsicInterior_singleton])
  have hpS : p ∈ S :=
    (show (⟨p, hpL⟩ : L.space) ∈ Subtype.val ⁻¹' S from mem_of_mem_nhds hnS)
  have hpd : p ∈ d i := (hSdq hpS).1
  have hpint : (e i ⟨p, hpd⟩ : F) ∈ interior (C i) := by
    by_contra hnot
    exact (hSdq hpS).2 ((hboundary i ⟨p, hpd⟩).mpr
      ⟨subset_closure (e i ⟨p, hpd⟩).property, hnot⟩)
  have hrep (x : d i) : (e i x : F) = g i x :=
    (heval i x).trans ((hgf i x.property).symm)
  have hdsL : d i ⊆ L.space := fun x hx => hLK.space_eq.symm.subset (hsub i hx)
  have hchart := (e i).injOn_and_interior_image_of_carrier_neighborhood
    (g i) hrep hdsL (hSdq.trans sdiff_subset) hpd hpint hnS
  have hgL : L.AffineOnFaces (g i) := (hLD.trans hDT).affineOnFaces (hgT i)
  exact ⟨g i, (fun s hs => hgL s hs.1), hchart⟩






theorem exists_faceAffine_vertex_stars_of_local_ball_pairs
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hlocal : ∀ x : K.space, ∃ d q : Set E,
      IsFinitePLBallPair F d q ∧ d ⊆ K.space ∧ (x : E) ∈ d \ q ∧
        IsOpen ((Subtype.val : K.space → E) ⁻¹' (d \ q)))
    (A : E →ᵃ[ℝ] ℝ) :
    ∃ L : SimplicialComplex ℝ E, L.faces.Finite ∧ L.IsSubdivision K ∧
      L.RespectsAffineHyperplane A ∧
      ∀ p : E, {p} ∈ L.faces → ∃ f : E → F,
        (L.closedFaceStar {p}).AffineOnFaces f ∧
        InjOn f (L.closedFaceStar {p}).space ∧
        f p ∈ interior (f '' (L.closedFaceStar {p}).space) := by
  classical
  let : CompactSpace K.space := isCompact_iff_compactSpace.mp (K.isCompact_space_of_finite hK)
  choose d q hball hsub hx hopen using hlocal
  let U : K.space → Set K.space := fun x => Subtype.val ⁻¹' (d x \ q x)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hopen
    (fun x _ => mem_iUnion.mpr ⟨x, hx x⟩)
  apply K.exists_faceAffine_vertex_stars_of_finite_ball_cover hK
    (fun x : t => d x) (fun x : t => q x) (fun x => hball x)
    (fun x => hsub x) (fun x => hopen x) ?_ A
  intro x
  obtain ⟨y, hyt, hy⟩ := mem_iUnion₂.mp (ht (mem_univ x))
  exact ⟨⟨y, hyt⟩, hy⟩

end Geometry.SimplicialComplex
