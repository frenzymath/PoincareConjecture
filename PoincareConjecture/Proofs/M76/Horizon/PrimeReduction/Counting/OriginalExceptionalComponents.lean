import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.OriginalFaceRectangleData
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteFaceCounts
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.ClosedAttachmentComponentCarriers










set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt

theorem OriginalFaceRectangles.cut_subset_original_complement
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
    {K : SimplicialComplex ℝ E} {g : E → X} {S : Set X} {s : Finset E}
    (D : OriginalFaceRectangles K g S s) (hs : s ∈ K.faces) (hgi : InjOn g K.space) :
    convexHull ℝ (s : Set E) \ ⋃ i, D.arc i ⊆ K.space \ g ⁻¹' S := by
  rintro x ⟨hx,hxoff⟩
  refine ⟨K.convexHull_subset_space hs hx,?_⟩
  intro hxS
  obtain ⟨y,hy,hgy⟩ := D.arcPhysical.symm.subset ⟨hxS,mem_image_of_mem g hx⟩
  have hyK := K.convexHull_subset_space hs (D.arcSubset hy)
  exact hxoff ((hgi hyK (K.convexHull_subset_space hs hx) hgy) ▸ hy)

theorem exists_original_exceptional_component_bound
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (g : E → X) (hgi : InjOn g K.space) (S : Set X)
    (D : ∀ s : K.FaceOfCard 3, OriginalFaceRectangles K g S s.1) :
    ∃ bad : Set (ConnectedComponents (K.space \ g ⁻¹' S : Set E)),
      bad.Finite ∧ bad.ncard ≤ 4 * Nat.card (K.FaceOfCard 3) ∧
      (∀ (s : K.FaceOfCard 3)
        (x : (convexHull ℝ (s.1 : Set E) \ ⋃ i, (D s).arc i : Set E)),
        ConnectedComponents.mk x ∈ (D s).exceptional →
        ConnectedComponents.mk
          (⟨x,(D s).cut_subset_original_complement s.2.1 hgi x.property⟩ :
            (K.space \ g ⁻¹' S : Set E)) ∈ bad) ∧
      ∀ c ∈ bad, ∃ (s : K.FaceOfCard 3)
        (x : (convexHull ℝ (s.1 : Set E) \ ⋃ i, (D s).arc i : Set E)),
        ConnectedComponents.mk x ∈ (D s).exceptional ∧
        ConnectedComponents.mk
          (⟨x,(D s).cut_subset_original_complement s.2.1 hgi x.property⟩ :
            (K.space \ g ⁻¹' S : Set E)) = c := by
  classical
  let := K.finite_faceOfCard hK 3
  let := Fintype.ofFinite (K.FaceOfCard 3)
  let C (s : K.FaceOfCard 3) := convexHull ℝ (s.1 : Set E) \ ⋃ i, (D s).arc i
  let inc (s : K.FaceOfCard 3) : C s → (K.space \ g ⁻¹' S : Set E) :=
    fun x => ⟨x,(D s).cut_subset_original_complement s.2.1 hgi x.property⟩
  have hc (s : K.FaceOfCard 3) : Continuous (inc s) :=
    continuous_subtype_val.subtype_mk _
  let point (s : K.FaceOfCard 3) (c : ConnectedComponents (C s)) : C s :=
    Classical.choose (ConnectedComponents.surjective_coe c)
  have hpoint (s : K.FaceOfCard 3) (c : ConnectedComponents (C s)) :
      ConnectedComponents.mk (point s c) = c :=
    Classical.choose_spec (ConnectedComponents.surjective_coe c)
  letI (s : K.FaceOfCard 3) : Finite ((D s).exceptional) := (D s).exceptionalFinite.to_subtype
  let Token := Σ s : K.FaceOfCard 3, (D s).exceptional
  let mark (z : Token) := ConnectedComponents.mk (inc z.1 (point z.1 z.2))
  have hmark (s : K.FaceOfCard 3) (x : C s)
      (hx : ConnectedComponents.mk x ∈ (D s).exceptional) :
      ConnectedComponents.mk (inc s x) = mark ⟨s,⟨ConnectedComponents.mk x,hx⟩⟩ := by
    have heq := ConnectedComponents.coe_eq_coe.mp (hpoint s (ConnectedComponents.mk x))
    have hxpoint : x ∈ connectedComponent (point s (ConnectedComponents.mk x)) := by
      rw [heq]
      exact mem_connectedComponent
    exact ConnectedComponents.coe_eq_coe'.mpr
      ((hc s).mapsTo_connectedComponent (point s (ConnectedComponents.mk x)) hxpoint)
  have hcard : Nat.card Token ≤ 4 * Nat.card (K.FaceOfCard 3) := by
    calc
      Nat.card Token = ∑ s : K.FaceOfCard 3, Nat.card ((D s).exceptional) := Nat.card_sigma
      _ ≤ ∑ _s : K.FaceOfCard 3, 4 := Finset.sum_le_sum
        (fun s _ => by simpa only [Nat.card_coe_set_eq] using (D s).exceptionalBound)
      _ = 4 * Nat.card (K.FaceOfCard 3) := by simp [Nat.card_eq_fintype_card,Nat.mul_comm]
  refine ⟨range mark,finite_range mark,?_,?_,?_⟩
  · have hle : (range mark).ncard ≤ Nat.card Token := by
      simpa only [image_univ,ncard_univ] using
        (ncard_image_le (s := (univ : Set Token)) (f := mark))
    exact hle.trans hcard
  · intro s x hx
    exact ⟨⟨s,⟨ConnectedComponents.mk x,hx⟩⟩,(hmark s x hx).symm⟩
  · rintro c ⟨⟨s,z⟩,rfl⟩
    exact ⟨s,point s z,(hpoint s z).symm ▸ z.property,rfl⟩

theorem original_cut_ball_component_class
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
    (K : SimplicialComplex ℝ E) (g : E → X) {S : Set X}
    {t : Finset E} (ht : t ∈ K.faces) {B : Set E}
    (hB : B ⊆ convexHull ℝ (t : Set E))
    (hcomp : ∀ x ∈ B \ g ⁻¹' S,
      connectedComponentIn (convexHull ℝ (t : Set E) \ g ⁻¹' S) x = B \ g ⁻¹' S)
    {x y : E} (hx : x ∈ B \ g ⁻¹' S) (hy : y ∈ B \ g ⁻¹' S) :
    ConnectedComponents.mk
      (⟨y,K.convexHull_subset_space ht (hB hy.1),hy.2⟩ : (K.space \ g ⁻¹' S : Set E)) =
    ConnectedComponents.mk
      (⟨x,K.convexHull_subset_space ht (hB hx.1),hx.2⟩ : (K.space \ g ⁻¹' S : Set E)) := by
  apply (Topology.mem_componentIn_iff_component_class
    (show x ∈ K.space \ g ⁻¹' S from ⟨K.convexHull_subset_space ht (hB hx.1),hx.2⟩)
    (show y ∈ K.space \ g ⁻¹' S from ⟨K.convexHull_subset_space ht (hB hy.1),hy.2⟩)).mp
  exact connectedComponentIn_mono x
    (sdiff_subset_sdiff_left (K.convexHull_subset_space ht)) ((hcomp x hx).symm.subset hy)

end PoincareConjecture.M76.PrismBelt
