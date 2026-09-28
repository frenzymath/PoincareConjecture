import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.OriginalRegularCoreMidpoint



set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1

def OriginalComponentCutCell
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
    {K : SimplicialComplex ℝ E} {g : E → X} {S : Set X}
    (D : ∀ s : K.FaceOfCard 3, OriginalFaceRectangles K g S s.1)
    (F : OriginalTetrahedralCutFamily K g S) (x : E) :=
  {j : RegularOriginalCutCell K g S D F.BallIndex F.ball //
    ((F.ball j.1.1 j.1.2 \ g ⁻¹' S) ∩ connectedComponentIn (K.space \ g ⁻¹' S) x).Nonempty}

set_option maxHeartbeats 600000 in
theorem original_trimmed_component_connected
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
    (C : ∀ j : RegularOriginalCutCell K g S D F.BallIndex F.ball,
      (F.cut j.1.1 (i₀ j) ×ˢ I : Set (E × ℝ)) ≃ₜ prismTrim (H j))
    (havoid : Disjoint (⋃ j, prismTrim (H j)) (g ⁻¹' S))
    (m : C((⋃ j : RegularOriginalCutCell K g S D F.BallIndex F.ball,
        F.ball j.1.1 j.1.2 \ g ⁻¹' S), (⋃ j, prismTrim (H j))))
    (hm : ∀ j (y : (F.ball j.1.1 j.1.2 \ g ⁻¹' S : Set E)),
      (m ⟨y,mem_iUnion.mpr ⟨j,y.property⟩⟩ : E) = prismFiberMidpoint (H j) ⟨y,y.property.1⟩)
    (x : (K.space \ g ⁻¹' S : Set E)) (hx : ConnectedComponents.mk x ∉ bad) :
    IsCompact (⋃ j : OriginalComponentCutCell D F (x : E), prismTrim (H j.1)) ∧
    IsConnected (⋃ j : OriginalComponentCutCell D F (x : E), prismTrim (H j.1)) ∧
    (⋃ j : OriginalComponentCutCell D F (x : E), prismTrim (H j.1)) ⊆
      connectedComponentIn (K.space \ g ⁻¹' S) (x : E) := by
  classical
  let Cell := RegularOriginalCutCell K g S D F.BallIndex F.ball
  let Index := OriginalComponentCutCell D F (x : E)
  let P := connectedComponentIn (K.space \ g ⁻¹' S) (x : E)
  let T := ⋃ j : Index, prismTrim (H j.1)
  let U := ⋃ j : Cell, F.ball j.1.1 j.1.2 \ g ⁻¹' S
  letI : Finite (K.FaceOfCard 4) := K.finite_faceOfCard hK 4
  letI (t : K.FaceOfCard 4) : Finite (F.BallIndex t) := F.finite_ball t
  letI : Finite Cell := by dsimp [Cell,RegularOriginalCutCell]; infer_instance
  letI : Finite Index := by dsimp [Index,OriginalComponentCutCell]; infer_instance
  have hcover : P = ⋃ j : Index, F.ball j.1.1.1 j.1.1.2 \ g ⁻¹' S :=
    nonexceptional_component_eq_regular_cell_cores K g hgi hpure D F bad hbad x hx
  have hcore (j : Index) : F.ball j.1.1.1 j.1.1.2 \ g ⁻¹' S ⊆ P :=
    fun _ hy => hcover.symm.subset (mem_iUnion.mpr ⟨j,hy⟩)
  have htrimcore (j : Cell) : prismTrim (H j) ⊆ F.ball j.1.1 j.1.2 \ g ⁻¹' S :=
    fun _ hy => ⟨prismTrim_subset (H j) hy,
      fun hS => disjoint_left.mp havoid (mem_iUnion.mpr ⟨j,hy⟩) hS⟩
  have hsub : T ⊆ P := iUnion_subset (fun j => (htrimcore j.1).trans (hcore j))
  have hcompact (j : Index) : IsCompact (prismTrim (H j.1)) := by
    letI : CompactSpace (F.cut j.1.1.1 (i₀ j.1) ×ˢ I : Set (E × ℝ)) :=
      isCompact_iff_compactSpace.mp ((F.disk_pair j.1.1.1 (i₀ j.1)).isCompact.prod isCompact_Icc)
    letI : CompactSpace (prismTrim (H j.1)) := (C j.1).compactSpace
    exact isCompact_iff_compactSpace.mpr inferInstance
  have hconnected (j : Index) : IsConnected (prismTrim (H j.1)) := by
    exact isConnected_iff_connectedSpace.mpr ((C j.1).symm.connectedSpace_iff.mpr
      (isConnected_iff_connectedSpace.mp
        ((F.disk_pair j.1.1.1 (i₀ j.1)).isConnected.prod (isConnected_Icc (by norm_num)))))
  have hPU : P ⊆ U := by
    intro y hy
    obtain ⟨j,hj⟩ := mem_iUnion.mp (hcover.subset hy)
    exact mem_iUnion.mpr ⟨j.1,hj⟩
  let f : C(P,E) :=
    ⟨fun y => (m ⟨y,hPU y.property⟩ : E),
      continuous_subtype_val.comp (m.continuous.comp (continuous_subtype_val.subtype_mk _))⟩
  have hfvalue (j : Index) (y : P) (hy : (y : E) ∈ F.ball j.1.1.1 j.1.1.2) :
      f y = prismFiberMidpoint (H j.1) ⟨y,hy⟩ := by
    have hyS := (connectedComponentIn_subset (K.space \ g ⁻¹' S) (x : E) y.property).2
    exact hm j.1 ⟨y,hy,hyS⟩
  let M := range f
  have hMconn : IsConnected M := by
    letI : ConnectedSpace P :=
      isConnected_iff_connectedSpace.mp (isConnected_connectedComponentIn_iff.mpr x.property)
    simpa only [image_univ] using isConnected_univ.image f f.continuous.continuousOn
  have hMT : M ⊆ T := by
    rintro _ ⟨y,rfl⟩
    obtain ⟨j,hj⟩ := mem_iUnion.mp (hcover.subset y.property)
    exact mem_iUnion.mpr ⟨j,(hfvalue j y hj.1).symm ▸ prismFiberMidpoint_mem_trim (H j.1) _⟩
  have hmeet (j : Index) : (prismTrim (H j.1) ∩ M).Nonempty := by
    obtain ⟨y,hy,hyp⟩ := j.property
    refine ⟨f ⟨y,hyp⟩,?_,⟨⟨y,hyp⟩,rfl⟩⟩
    rw [hfvalue j ⟨y,hyp⟩ hy.1]
    exact prismFiberMidpoint_mem_trim (H j.1) _
  have heq : (⋃ j : Index, prismTrim (H j.1) ∪ M) = T := by
    apply Subset.antisymm
    · exact iUnion_subset (fun j => union_subset
        (show prismTrim (H j.1) ⊆ T from subset_iUnion (fun j : Index => prismTrim (H j.1)) j) hMT)
    · exact iUnion_mono (fun j => subset_union_left)
  have hpre : IsPreconnected T := by
    rw [← heq]
    apply isPreconnected_iUnion
    · obtain ⟨y,hy⟩ := hMconn.nonempty
      exact ⟨y,mem_iInter.mpr (fun _ => Or.inr hy)⟩
    · intro j
      exact ((hconnected j).union (hmeet j) hMconn).isPreconnected
  exact ⟨isCompact_iUnion hcompact,⟨hMconn.nonempty.mono hMT,hpre⟩,hsub⟩

theorem original_trimmed_component_eq_connectedComponentIn
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
    (K : SimplicialComplex ℝ E) (g : E → X) {S : Set X}
    (D : ∀ s : K.FaceOfCard 3, OriginalFaceRectangles K g S s.1)
    (F : OriginalTetrahedralCutFamily K g S)
    (i₀ : ∀ j : RegularOriginalCutCell K g S D F.BallIndex F.ball, F.DiskIndex j.1.1)
    (H : ∀ j : RegularOriginalCutCell K g S D F.BallIndex F.ball,
      (F.cut j.1.1 (i₀ j) ×ˢ I : Set (E × ℝ)) ≃ₜ F.ball j.1.1 j.1.2)
    (havoid : Disjoint (⋃ j, prismTrim (H j)) (g ⁻¹' S))
    (x : E)
    (hconn : IsConnected (⋃ j : OriginalComponentCutCell D F x, prismTrim (H j.1)))
    (hsub : (⋃ j : OriginalComponentCutCell D F x, prismTrim (H j.1)) ⊆
      connectedComponentIn (K.space \ g ⁻¹' S) x)
    {z : E} (hz : z ∈ ⋃ j : OriginalComponentCutCell D F x, prismTrim (H j.1)) :
    connectedComponentIn (⋃ j, prismTrim (H j)) z =
      ⋃ j : OriginalComponentCutCell D F x, prismTrim (H j.1) := by
  have hUP : (⋃ j, prismTrim (H j)) ⊆ K.space \ g ⁻¹' S := by
    intro y hy
    obtain ⟨j,hj⟩ := mem_iUnion.mp hy
    exact ⟨K.convexHull_subset_space j.1.1.2.1
      (F.ball_subset_tetrahedron j.1.1 j.1.2 (prismTrim_subset (H j) hj)),
      fun hS => disjoint_left.mp havoid (mem_iUnion.mpr ⟨j,hj⟩) hS⟩
  apply Subset.antisymm
  · intro y hy
    have hyP := connectedComponentIn_mono z hUP hy
    rw [← connectedComponentIn_eq (hsub hz)] at hyP
    have hyU := connectedComponentIn_subset (⋃ j, prismTrim (H j)) z hy
    obtain ⟨j,hj⟩ := mem_iUnion.mp hyU
    have hyS := (hUP (mem_iUnion.mpr ⟨j,hj⟩)).2
    exact mem_iUnion.mpr ⟨⟨j,⟨y,⟨prismTrim_subset (H j) hj,hyS⟩,hyP⟩⟩,hj⟩
  · apply hconn.isPreconnected.subset_connectedComponentIn hz
    exact iUnion_subset (fun j => subset_iUnion (fun j => prismTrim (H j)) j.1)

local notation "Square" => (I ×ˢ I : Set (ℝ × ℝ))

theorem original_nonexceptional_trimmed_component
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
    (i₀ : ∀ j : RegularOriginalCutCell K g S D F.BallIndex F.ball, F.DiskIndex j.1.1)
    (H : ∀ j : RegularOriginalCutCell K g S D F.BallIndex F.ball,
      (F.cut j.1.1 (i₀ j) ×ˢ I : Set (E × ℝ)) ≃ₜ F.ball j.1.1 j.1.2)
    (flip : ∀ j : RegularOriginalCutCell K g S D F.BallIndex F.ball,
      CutBallRectangle (fun f : TetrahedronFace K j.1.1.1 => D f.1) (F.ball j.1.1 j.1.2) → Bool)
    (hformula : ∀ j (z : CutBallRectangle (fun f : TetrahedronFace K j.1.1.1 => D f.1)
      (F.ball j.1.1 j.1.2)) (u t : I),
      ((H j).symm ⟨G z.1.1.1 z.1.2
        ⟨(u,fiberFlip (flip j z) t),u.property,(fiberFlip (flip j z) t).property⟩,
        z.2 (G _ _ _).property⟩ : E × ℝ) =
        ((G z.1.1.1 z.1.2
          ⟨(u,fiberFlip (flip j z) 0),u.property,(fiberFlip (flip j z) 0).property⟩ : E),(t : ℝ)))
    (C : ∀ j : RegularOriginalCutCell K g S D F.BallIndex F.ball,
      (F.cut j.1.1 (i₀ j) ×ˢ I : Set (E × ℝ)) ≃ₜ prismTrim (H j))
    (havoid : Disjoint (⋃ j, prismTrim (H j)) (g ⁻¹' S))
    (x : (K.space \ g ⁻¹' S : Set E)) (hx : ConnectedComponents.mk x ∉ bad) :
    IsCompact (⋃ j : OriginalComponentCutCell D F (x : E), prismTrim (H j.1)) ∧
    IsConnected (⋃ j : OriginalComponentCutCell D F (x : E), prismTrim (H j.1)) ∧
    (⋃ j : OriginalComponentCutCell D F (x : E), prismTrim (H j.1)) ⊆
      connectedComponentIn (K.space \ g ⁻¹' S) (x : E) ∧
    ∀ z ∈ (⋃ j : OriginalComponentCutCell D F (x : E), prismTrim (H j.1)),
      connectedComponentIn (⋃ j, prismTrim (H j)) z =
        ⋃ j : OriginalComponentCutCell D F (x : E), prismTrim (H j.1) := by
  obtain ⟨m,hm⟩ := exists_original_regular_core_midpoint K hK g hgi D G hW hZ hL haffine
    F i₀ H flip hformula
  obtain ⟨hcompact,hconn,hsub⟩ := original_trimmed_component_connected K hK g hgi hpure
    D F bad hbad i₀ H C havoid m hm x hx
  exact ⟨hcompact,hconn,hsub,fun _ hz =>
    original_trimmed_component_eq_connectedComponentIn K g D F i₀ H havoid x hconn hsub hz⟩

end PoincareConjecture.M76.PrismBelt
