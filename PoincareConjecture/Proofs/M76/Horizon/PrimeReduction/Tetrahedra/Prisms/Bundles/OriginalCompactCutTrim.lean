import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.CompactOriginalPrismCoreMargin
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.OriginalVariableTrimmedReflection
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.VariableTrimmedComponent



set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1
local notation "Square" => (I ×ˢ I : Set (ℝ × ℝ))

set_option maxHeartbeats 800000 in
theorem exists_original_compact_cut_trim
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (g : E → X) (hgi : InjOn g K.space)
    {S : Set X} (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 4)
    (D : ∀ s : K.FaceOfCard 3, OriginalFaceRectangles K g S s.1)
    (G : ∀ s k, Square ≃ₜ (D s).carrier k)
    (hW : ∀ s k y, (G s k y : E) ∈ (D s).arc ((D s).cap k false) ↔ (y : ℝ × ℝ).2 = 0)
    (hZ : ∀ s k y, (G s k y : E) ∈ (D s).arc ((D s).cap k true) ↔ (y : ℝ × ℝ).2 = 1)
    (hL : ∀ s k b y, (G s k y : E) ∈ (D s).side k b ↔ (y : ℝ × ℝ).1 = if b then 1 else 0)
    (haffine : ∀ s k b t, (G s k (sidePoint b t) : E) =
      AffineMap.lineMap (G s k (sidePoint b 0) : E) (G s k (sidePoint b 1) : E) (t : ℝ))
    (F : OriginalTetrahedralCutFamily K g S)
    (bad : Set (ConnectedComponents (K.space \ g ⁻¹' S : Set E)))
    (hbad : ∀ (s : K.FaceOfCard 3)
      (y : (convexHull ℝ (s.1 : Set E) \ ⋃ i, (D s).arc i : Set E)),
      ConnectedComponents.mk y ∈ (D s).exceptional →
      ConnectedComponents.mk
        (⟨y,(D s).cut_subset_original_complement s.2.1 hgi y.property⟩ :
          (K.space \ g ⁻¹' S : Set E)) ∈ bad)
    (i₀ i₁ : ∀ j : RegularOriginalCutCell K g S D F.BallIndex F.ball, F.DiskIndex j.1.1)
    (hne : ∀ j, i₀ j ≠ i₁ j)
    (hcap : ∀ j, F.cut j.1.1 (i₀ j) ⊆ F.boundary j.1.1 j.1.2 ∧
      F.cut j.1.1 (i₁ j) ⊆ F.boundary j.1.1 j.1.2)
    (H : ∀ j : RegularOriginalCutCell K g S D F.BallIndex F.ball,
      (F.cut j.1.1 (i₀ j) ×ˢ I : Set (E × ℝ)) ≃ₜ F.ball j.1.1 j.1.2)
    (hH : ∀ j, (H j).IsFinitePL)
    (hzero : ∀ j y, (H j y : E) ∈ F.cut j.1.1 (i₀ j) ↔ (y : E × ℝ).2 = 0)
    (hone : ∀ j y, (H j y : E) ∈ F.cut j.1.1 (i₁ j) ↔ (y : E × ℝ).2 = 1)
    (flip : ∀ j : RegularOriginalCutCell K g S D F.BallIndex F.ball,
      CutBallRectangle (fun f : TetrahedronFace K j.1.1.1 => D f.1) (F.ball j.1.1 j.1.2) → Bool)
    (hformula : ∀ j (z : CutBallRectangle (fun f : TetrahedronFace K j.1.1.1 => D f.1)
      (F.ball j.1.1 j.1.2)) (u t : I),
      ((H j).symm ⟨G z.1.1.1 z.1.2
        ⟨(u,fiberFlip (flip j z) t),u.property,(fiberFlip (flip j z) t).property⟩,
        z.2 (G _ _ _).property⟩ : E × ℝ) =
        ((G z.1.1.1 z.1.2
          ⟨(u,fiberFlip (flip j z) 0),u.property,(fiberFlip (flip j z) 0).property⟩ : E),(t : ℝ)))
    (Q : Set E) (hQ : IsCompact Q) (hQS : Disjoint Q (g ⁻¹' S)) :
    ∃ (δ : ℝ) (hδ : 0 < δ) (hhalf : δ < 1/2), δ ≤ 1/4 ∧
    ∃ C : ∀ j : RegularOriginalCutCell K g S D F.BallIndex F.ball,
      (F.cut j.1.1 (i₀ j) ×ˢ I : Set (E × ℝ)) ≃ₜ prismTrimAt (H j) δ,
      (∀ j, (C j).IsFinitePL) ∧
      (∀ j x, (C j x : E) = H j (trimProductAt (F.cut j.1.1 (i₀ j)) δ hδ hhalf x)) ∧
      Disjoint (⋃ j, prismTrimAt (H j) δ) (g ⁻¹' S) ∧
      (∀ j, Q ∩ F.ball j.1.1 j.1.2 ⊆ prismTrimAt (H j) δ) ∧
      (∀ (x : (K.space \ g ⁻¹' S : Set E)), ConnectedComponents.mk x ∉ bad →
        IsCompact (⋃ j : OriginalComponentCutCell D F (x : E), prismTrimAt (H j.1) δ) ∧
        IsConnected (⋃ j : OriginalComponentCutCell D F (x : E), prismTrimAt (H j.1) δ) ∧
        (⋃ j : OriginalComponentCutCell D F (x : E), prismTrimAt (H j.1) δ) ⊆
          connectedComponentIn (K.space \ g ⁻¹' S) (x : E) ∧
        connectedComponentIn (K.space \ g ⁻¹' S) (x : E) ∩ Q ⊆
          (⋃ j : OriginalComponentCutCell D F (x : E), prismTrimAt (H j.1) δ) ∧
        ∀ z ∈ (⋃ j : OriginalComponentCutCell D F (x : E), prismTrimAt (H j.1) δ),
          connectedComponentIn (⋃ j, prismTrimAt (H j) δ) z =
            ⋃ j : OriginalComponentCutCell D F (x : E), prismTrimAt (H j.1) δ) ∧
    ∃ J : (⋃ j, prismTrimAt (H j) δ) ≃ₜ (⋃ j, prismTrimAt (H j) δ),
      J.IsFinitePL ∧ Function.Involutive J ∧
      (∀ j (x : prismTrimAt (H j) δ),
        (J ⟨x,mem_iUnion.mpr ⟨j,x.property⟩⟩ : E) = prismFiberReflection (C j) x) ∧
      ∀ j (x : prismTrimAt (H j) δ),
        (((C j).symm x : E × ℝ).2 = 0 ∨ ((C j).symm x : E × ℝ).2 = 1) →
        (J ⟨x,mem_iUnion.mpr ⟨j,x.property⟩⟩ : E) ≠ x := by
  classical
  obtain ⟨δ,hδ,hhalf,hsmall,hmargin⟩ := exists_original_compact_cut_prism_margin
    K hK g hgi D F i₀ i₁ H hzero hone Q hQ hQS
  obtain ⟨C,hC,hCv,havoid,J,hJ,hinv,hJv,hfree⟩ := exists_original_variable_trimmed_reflection
    K hK g hgi D G hW hZ hL haffine F i₀ i₁ hne hcap H hH hzero hone flip hformula δ hδ hhalf
  choose C₀ hC₀ hC₀v using fun j => exists_finitePL_symmetric_prism_trim (H j) (hH j)
  have havoid₀ : Disjoint (⋃ j, prismTrim (H j)) (g ⁻¹' S) :=
    havoid.mono_left (iUnion_mono (fun j => prismTrim_subset_trimAt (H j) hsmall))
  refine ⟨δ,hδ,hhalf,hsmall,C,hC,hCv,havoid,?_,?_,J,hJ,hinv,hJv,hfree⟩
  · intro j y hy
    exact ⟨hy.2,hmargin j ⟨y,hy.2⟩ hy.1⟩
  · intro x hx
    have hfixed := (original_nonexceptional_trimmed_component K hK g hgi hpure D G
      hW hZ hL haffine F bad hbad i₀ H flip hformula C₀ havoid₀ x hx).2.1
    exact original_variable_trimmed_component K hK g hgi hpure D F bad hbad i₀ H C₀
      δ hsmall C havoid Q hmargin x hx hfixed

end PoincareConjecture.M76.PrismBelt
