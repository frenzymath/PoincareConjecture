import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.OriginalTrimmedComponent
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.VariableSymmetricPrismTrim

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1

theorem prismTrim_subset_trimAt
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {A : Set E} {B : Set X}
    (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B) {δ : ℝ} (hδ : δ ≤ 1/4) :
    prismTrim H ⊆ prismTrimAt H δ := by
  intro x hx
  have hxB := prismTrim_subset H hx
  have hh := (mem_prismTrim_iff H ⟨x,hxB⟩).mp hx
  exact ⟨hxB,by constructor <;> linarith [hh.1,hh.2]⟩

set_option maxHeartbeats 600000 in
theorem original_variable_trimmed_component
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (g : E → X) (hgi : InjOn g K.space)
    {S : Set X} (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 4)
    (D : ∀ s : K.FaceOfCard 3, OriginalFaceRectangles K g S s.1)
    (F : OriginalTetrahedralCutFamily K g S)
    (bad : Set (ConnectedComponents (K.space \ g ⁻¹' S : Set E)))
    (hbad : ∀ (s : K.FaceOfCard 3)
      (y : (convexHull ℝ (s.1 : Set E) \ ⋃ i, (D s).arc i : Set E)),
      ConnectedComponents.mk y ∈ (D s).exceptional →
      ConnectedComponents.mk
        (⟨y,(D s).cut_subset_original_complement s.2.1 hgi y.property⟩ :
          (K.space \ g ⁻¹' S : Set E)) ∈ bad)
    (i₀ : ∀ j : RegularOriginalCutCell K g S D F.BallIndex F.ball, F.DiskIndex j.1.1)
    (H : ∀ j : RegularOriginalCutCell K g S D F.BallIndex F.ball,
      (F.cut j.1.1 (i₀ j) ×ˢ I : Set (E × ℝ)) ≃ₜ F.ball j.1.1 j.1.2)
    (C₀ : ∀ j : RegularOriginalCutCell K g S D F.BallIndex F.ball,
      (F.cut j.1.1 (i₀ j) ×ˢ I : Set (E × ℝ)) ≃ₜ prismTrim (H j))
    (δ : ℝ) (hsmall : δ ≤ 1/4)
    (C : ∀ j : RegularOriginalCutCell K g S D F.BallIndex F.ball,
      (F.cut j.1.1 (i₀ j) ×ˢ I : Set (E × ℝ)) ≃ₜ prismTrimAt (H j) δ)
    (havoid : Disjoint (⋃ j, prismTrimAt (H j) δ) (g ⁻¹' S))
    (Q : Set E)
    (hmargin : ∀ j (y : F.ball j.1.1 j.1.2), (y : E) ∈ Q →
      δ ≤ ((H j).symm y : E × ℝ).2 ∧ ((H j).symm y : E × ℝ).2 ≤ 1-δ)
    (x : (K.space \ g ⁻¹' S : Set E)) (hx : ConnectedComponents.mk x ∉ bad)
    (hfixed : IsConnected (⋃ j : OriginalComponentCutCell D F (x : E), prismTrim (H j.1))) :
    IsCompact (⋃ j : OriginalComponentCutCell D F (x : E), prismTrimAt (H j.1) δ) ∧
    IsConnected (⋃ j : OriginalComponentCutCell D F (x : E), prismTrimAt (H j.1) δ) ∧
    (⋃ j : OriginalComponentCutCell D F (x : E), prismTrimAt (H j.1) δ) ⊆
      connectedComponentIn (K.space \ g ⁻¹' S) (x : E) ∧
    connectedComponentIn (K.space \ g ⁻¹' S) (x : E) ∩ Q ⊆
      (⋃ j : OriginalComponentCutCell D F (x : E), prismTrimAt (H j.1) δ) ∧
    ∀ z ∈ (⋃ j : OriginalComponentCutCell D F (x : E), prismTrimAt (H j.1) δ),
      connectedComponentIn (⋃ j, prismTrimAt (H j) δ) z =
        ⋃ j : OriginalComponentCutCell D F (x : E), prismTrimAt (H j.1) δ := by
  classical
  let Cell := RegularOriginalCutCell K g S D F.BallIndex F.ball
  let Index := OriginalComponentCutCell D F (x : E)
  let P := connectedComponentIn (K.space \ g ⁻¹' S) (x : E)
  let T₀ := ⋃ j : Index, prismTrim (H j.1)
  let T := ⋃ j : Index, prismTrimAt (H j.1) δ
  let U := ⋃ j : Cell, prismTrimAt (H j) δ
  letI : Finite (K.FaceOfCard 4) := K.finite_faceOfCard hK 4
  letI (t : K.FaceOfCard 4) : Finite (F.BallIndex t) := F.finite_ball t
  letI : Finite Cell := by dsimp [Cell,RegularOriginalCutCell]; infer_instance
  letI : Finite Index := by dsimp [Index,OriginalComponentCutCell]; infer_instance
  have hcover : P = ⋃ j : Index, F.ball j.1.1.1 j.1.1.2 \ g ⁻¹' S :=
    nonexceptional_component_eq_regular_cell_cores K g hgi hpure D F bad hbad x hx
  have hcore (j : Index) : F.ball j.1.1.1 j.1.1.2 \ g ⁻¹' S ⊆ P :=
    fun _ hy => hcover.symm.subset (mem_iUnion.mpr ⟨j,hy⟩)
  have htrimcore (j : Cell) : prismTrimAt (H j) δ ⊆ F.ball j.1.1 j.1.2 \ g ⁻¹' S :=
    fun _ hy => ⟨prismTrimAt_subset (H j) δ hy,
      fun hS => disjoint_left.mp havoid (mem_iUnion.mpr ⟨j,hy⟩) hS⟩
  have hsub : T ⊆ P := iUnion_subset (fun j => (htrimcore j.1).trans (hcore j))
  have hcompact (j : Index) : IsCompact (prismTrimAt (H j.1) δ) := by
    letI : CompactSpace (F.cut j.1.1.1 (i₀ j.1) ×ˢ I : Set (E × ℝ)) :=
      isCompact_iff_compactSpace.mp ((F.disk_pair j.1.1.1 (i₀ j.1)).isCompact.prod isCompact_Icc)
    letI : CompactSpace (prismTrimAt (H j.1) δ) := (C j.1).compactSpace
    exact isCompact_iff_compactSpace.mpr inferInstance
  have hconnected (j : Index) : IsConnected (prismTrimAt (H j.1) δ) :=
    isConnected_iff_connectedSpace.mpr ((C j.1).symm.connectedSpace_iff.mpr
      (isConnected_iff_connectedSpace.mp
        ((F.disk_pair j.1.1.1 (i₀ j.1)).isConnected.prod (isConnected_Icc (by norm_num)))))
  have hsmalltrim (j : Index) : prismTrim (H j.1) ⊆ prismTrimAt (H j.1) δ :=
    prismTrim_subset_trimAt (H j.1) hsmall
  have hT₀T : T₀ ⊆ T := iUnion_mono hsmalltrim
  have hmeet (j : Index) : (prismTrimAt (H j.1) δ ∩ T₀).Nonempty := by
    have hne : (prismTrim (H j.1)).Nonempty := by
      obtain ⟨a,ha⟩ := (F.disk_pair j.1.1.1 (i₀ j.1)).isConnected.nonempty
      exact ⟨C₀ j.1 ⟨(a,0),ha,le_rfl,zero_le_one⟩,(C₀ j.1 _).property⟩
    obtain ⟨a,ha⟩ := hne
    exact ⟨a,hsmalltrim j ha,mem_iUnion.mpr ⟨j,ha⟩⟩
  have heq : (⋃ j : Index, prismTrimAt (H j.1) δ ∪ T₀) = T := by
    apply Subset.antisymm
    · exact iUnion_subset (fun j => union_subset
        (show prismTrimAt (H j.1) δ ⊆ T from subset_iUnion (fun j : Index => prismTrimAt (H j.1) δ) j) hT₀T)
    · exact iUnion_mono (fun _ => subset_union_left)
  have hconn : IsConnected T := by
    refine ⟨hfixed.nonempty.mono hT₀T,?_⟩
    rw [← heq]
    apply isPreconnected_iUnion
    · obtain ⟨y,hy⟩ := hfixed.nonempty
      exact ⟨y,mem_iInter.mpr (fun _ => Or.inr hy)⟩
    · intro j
      exact ((hconnected j).union (hmeet j) hfixed).isPreconnected
  have hQP : P ∩ Q ⊆ T := by
    rintro y ⟨hyP,hyQ⟩
    obtain ⟨j,hj⟩ := mem_iUnion.mp (hcover.subset hyP)
    exact mem_iUnion.mpr ⟨j,hj.1,hmargin j.1 ⟨y,hj.1⟩ hyQ⟩
  refine ⟨isCompact_iUnion hcompact,hconn,hsub,hQP,?_⟩
  intro z hz
  have hUP : U ⊆ K.space \ g ⁻¹' S := by
    intro y hy
    obtain ⟨j,hj⟩ := mem_iUnion.mp hy
    exact ⟨K.convexHull_subset_space j.1.1.2.1
      (F.ball_subset_tetrahedron j.1.1 j.1.2 (htrimcore j hj).1),(htrimcore j hj).2⟩
  apply Subset.antisymm
  · intro y hy
    have hyP := connectedComponentIn_mono z hUP hy
    rw [← connectedComponentIn_eq (hsub hz)] at hyP
    obtain ⟨j,hj⟩ := mem_iUnion.mp (connectedComponentIn_subset U z hy)
    exact mem_iUnion.mpr ⟨⟨j,⟨y,htrimcore j hj,hyP⟩⟩,hj⟩
  · apply hconn.isPreconnected.subset_connectedComponentIn hz
    exact iUnion_subset (fun j => subset_iUnion (fun j => prismTrimAt (H j) δ) j.1)

end PoincareConjecture.M76.PrismBelt
