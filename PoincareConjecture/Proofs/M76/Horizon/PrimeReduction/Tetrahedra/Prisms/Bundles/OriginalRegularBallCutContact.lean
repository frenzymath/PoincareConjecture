import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Gluing.GlobalActualCutBallPrism
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.SymmetricPrismTrim



set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1
local notation "V3" => (Fin 3 → ℝ)

theorem original_regular_ball_cut_contact
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [Finite ι] [DecidableEq ι]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (g : E → X) (hgi : InjOn g K.space)
    {S : Set X} {t : Finset E} (ht : t ∈ K.faces) (ht4 : t.card = 4)
    (D : ∀ f : TetrahedronFace K t, OriginalFaceRectangles K g S f.1.1)
    (cut rim : ι → Set E) (hcut : ∀ i, IsFinitePLBallPair (ℝ × ℝ) (cut i) (rim i))
    (hsub : ∀ i, cut i ⊆ convexHull ℝ (t : Set E))
    (hrim : ∀ i, cut i ∩ intrinsicFrontier ℝ (convexHull ℝ (t : Set E)) = rim i)
    (hdis : Pairwise fun i j => Disjoint (cut i) (cut j))
    (hphysical : g '' (⋃ i, cut i) = S ∩ (g '' convexHull ℝ (t : Set E)))
    {B R : Set E} (hB : IsFinitePLBallPair V3 B R)
    (hR : R = B ∩ (intrinsicFrontier ℝ (convexHull ℝ (t : Set E)) ∪ ⋃ i, cut i))
    (hwhole : ∀ i, (B ∩ cut i).Nonempty → cut i ⊆ R)
    (hcomp : ∀ x ∈ B \ g ⁻¹' S,
      connectedComponentIn (convexHull ℝ (t : Set E) \ g ⁻¹' S) x = B \ g ⁻¹' S)
    (hregular : ∀ (f : TetrahedronFace K t)
      (x : (convexHull ℝ (f.1.1 : Set E) \ ⋃ i, (D f).arc i : Set E)),
      (x : E) ∈ B → ConnectedComponents.mk x ∉ (D f).exceptional)
    (i₀ i₁ : ι) (hne : i₀ ≠ i₁) (hi₀ : cut i₀ ⊆ R) (hi₁ : cut i₁ ⊆ R) :
    B ∩ (⋃ i, cut i) = cut i₀ ∪ cut i₁ := by
  classical
  obtain ⟨owner,_,hconn,_,hlabels⟩ := exists_actual_belt_distinct_cap_labels
    K hK g hgi ht ht4 D cut rim hcut hsub hrim hdis hphysical hB hR hwhole hcomp hregular
  obtain ⟨x,hx⟩ := hconn.nonempty
  obtain ⟨z,hz⟩ := mem_iUnion.mp hx
  have htwo (i : ι) (hi : cut i ⊆ R) : i = i₀ ∨ i = i₁ := by
    have ha := ((hlabels z).2 i₀).mp hi₀
    have hb := ((hlabels z).2 i₁).mp hi₁
    have hc := ((hlabels z).2 i).mp hi
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hc with hc | hc <;> grind
  ext x
  constructor
  · rintro ⟨hxB,hxC⟩
    obtain ⟨i,hi⟩ := mem_iUnion.mp hxC
    rcases htwo i (hwhole i ⟨x,hxB,hi⟩) with he | he
    · exact Or.inl (he ▸ hi)
    · exact Or.inr (he ▸ hi)
  · intro hx
    rcases hx with hx | hx
    · exact ⟨hB.1 (hi₀ hx),mem_iUnion.mpr ⟨i₀,hx⟩⟩
    · exact ⟨hB.1 (hi₁ hx),mem_iUnion.mpr ⟨i₁,hx⟩⟩

theorem prismTrim_disjoint_total_cut
    {E ι : Type*} [TopologicalSpace E] {A B : Set E}
    (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B) (cut : ι → Set E) (i₀ i₁ : ι)
    (hcontact : B ∩ (⋃ i, cut i) = cut i₀ ∪ cut i₁)
    (h₀ : ∀ x, (H x : E) ∈ cut i₀ ↔ (x : E × ℝ).2 = 0)
    (h₁ : ∀ x, (H x : E) ∈ cut i₁ ↔ (x : E × ℝ).2 = 1) :
    Disjoint (prismTrim H) (⋃ i, cut i) := by
  apply disjoint_left.mpr
  intro x hx hy
  exact disjoint_left.mp (prismTrim_disjoint_caps H h₀ h₁) hx
    (hcontact.subset ⟨prismTrim_subset H hx,hy⟩)

theorem prismTrim_disjoint_physical_cut
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : SimplicialComplex ℝ E) (g : E → X) (hgi : InjOn g K.space)
    {S : Set X} {t : Finset E} (ht : t ∈ K.faces) {A B : Set E}
    (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B) (hBsub : B ⊆ convexHull ℝ (t : Set E))
    (cut : ι → Set E) (hcut : (⋃ i, cut i) ⊆ convexHull ℝ (t : Set E))
    (hphysical : g '' (⋃ i, cut i) = S ∩ (g '' convexHull ℝ (t : Set E)))
    (havoid : Disjoint (prismTrim H) (⋃ i, cut i)) :
    Disjoint (prismTrim H) (g ⁻¹' S) := by
  apply disjoint_left.mpr
  intro x hx hxS
  exact disjoint_left.mp havoid hx ((original_face_cut_mem_iff K g hgi ht hcut hphysical
    (hBsub (prismTrim_subset H hx))).mpr hxS)

theorem disjoint_prismTrims_of_cut_contact
    {E : Type*} [TopologicalSpace E] {A₀ A₁ B₀ B₁ T : Set E}
    (H₀ : (A₀ ×ˢ I : Set (E × ℝ)) ≃ₜ B₀)
    (H₁ : (A₁ ×ˢ I : Set (E × ℝ)) ≃ₜ B₁)
    (hcontact : B₀ ∩ B₁ ⊆ T) (havoid : Disjoint (prismTrim H₀) T) :
    Disjoint (prismTrim H₀) (prismTrim H₁) := by
  apply disjoint_left.mpr
  intro x hx hy
  exact disjoint_left.mp havoid hx (hcontact ⟨prismTrim_subset H₀ hx,prismTrim_subset H₁ hy⟩)

end PoincareConjecture.M76.PrismBelt
