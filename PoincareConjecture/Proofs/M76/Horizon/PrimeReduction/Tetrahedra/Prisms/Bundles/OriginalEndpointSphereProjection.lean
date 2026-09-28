import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.OriginalPrismRescaling
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.EndpointCapProjection
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.EndpointOrbitCharts



set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1
local notation "Square" => (I ×ˢ I : Set (ℝ × ℝ))

set_option maxHeartbeats 4000000 in
theorem exists_original_endpoint_sphere_projection
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (g : E → X) (hgi : InjOn g K.space)
    {S : Set X} (D : ∀ s : K.FaceOfCard 3, OriginalFaceRectangles K g S s.1)
    (G : ∀ s k, Square ≃ₜ (D s).carrier k)
    (hW : ∀ s k y, (G s k y : E) ∈ (D s).arc ((D s).cap k false) ↔ (y : ℝ × ℝ).2 = 0)
    (hZ : ∀ s k y, (G s k y : E) ∈ (D s).arc ((D s).cap k true) ↔ (y : ℝ × ℝ).2 = 1)
    (hL : ∀ s k b y, (G s k y : E) ∈ (D s).side k b ↔ (y : ℝ × ℝ).1 = if b then 1 else 0)
    (haffine : ∀ s k b t, (G s k (sidePoint b t) : E) =
      AffineMap.lineMap (G s k (sidePoint b 0) : E) (G s k (sidePoint b 1) : E) (t : ℝ))
    (F : OriginalTetrahedralCutFamily K g S)
    (i₀ i₁ : ∀ j : RegularOriginalCutCell K g S D F.BallIndex F.ball, F.DiskIndex j.1.1)
    (H : ∀ j : RegularOriginalCutCell K g S D F.BallIndex F.ball,
      (F.cut j.1.1 (i₀ j) ×ˢ I : Set (E × ℝ)) ≃ₜ F.ball j.1.1 j.1.2)
    (hH : ∀ j, (H j).IsFinitePL)
    (hzero : ∀ j x, (H j x : E) ∈ F.cut j.1.1 (i₀ j) ↔ (x : E × ℝ).2 = 0)
    (hone : ∀ j x, (H j x : E) ∈ F.cut j.1.1 (i₁ j) ↔ (x : E × ℝ).2 = 1)
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
    (hC : ∀ j, (C j).IsFinitePL)
    (hCv : ∀ j x, (C j x : E) = H j (trimProduct (F.cut j.1.1 (i₀ j)) x))
    (havoid : Disjoint (⋃ j, prismTrim (H j)) (g ⁻¹' S)) :
    ∃ r : E → E,
      FinitePiecewiseAffineOn r (⋃ j, prismTrim (H j)) ∧
      FinitePiecewiseAffineOn r (⋃ j, prismEnds (C j)) ∧
      (∀ j x, r (C j x) = H j x) ∧
      r '' (⋃ j, prismEnds (C j)) = ⋃ j, prismEnds (H j) ∧
      (⋃ j, prismEnds (H j)) ⊆ K.space ∩ g ⁻¹' S ∧
      (∀ y, ((⋃ j, prismTrim (H j)) ∩ r ⁻¹' {y}).Finite ∧
        ((⋃ j, prismTrim (H j)) ∩ r ⁻¹' {y}).ncard ≤
          Nat.card (RegularOriginalCutCell K g S D F.BallIndex F.ball)) ∧
    ∃ π : C((⋃ j, prismEnds (C j)), (K.space ∩ g ⁻¹' S : Set E)),
      (∀ x, (π x : E) = r x) ∧
      (∀ j a b, (π (prismEndpointLift C j a b) : E) = prismEndMap (H j) a b) ∧
      ∀ y, (π ⁻¹' {y}).Finite := by
  classical
  let : Finite (K.FaceOfCard 4) := K.finite_faceOfCard hK 4
  let (t : K.FaceOfCard 4) : Finite (F.BallIndex t) := F.finite_ball t
  let : Finite (RegularOriginalCutCell K g S D F.BallIndex F.ball) := by
    unfold RegularOriginalCutCell
    infer_instance
  obtain ⟨r,hr,_,_,hrvalue,_⟩ := exists_original_prism_rescaling K hK g hgi D G hW hZ hL
    haffine F i₀ H hH flip hformula C hC hCv havoid 0 le_rfl (by norm_num)
  have hrval (j) (x) : r (C j x) = H j x := by
    rw [hrvalue]
    congr 2
    apply Subtype.ext
    simp [prismScaleProduct]
  have hrend := finitePL_on_prism_ends C hC hr
  have himage := image_prism_ends_of_cell_maps H C r hrval
  have hraw : (⋃ j, prismEnds (H j)) ⊆ K.space ∩ g ⁻¹' S := by
    intro y hy
    obtain ⟨j,⟨⟨a,b⟩,rfl⟩⟩ := mem_iUnion.mp hy
    have hB := (prismEndMap (H j) a b).property
    have ht := F.ball_subset_tetrahedron j.1.1 j.1.2 hB
    refine ⟨K.convexHull_subset_space j.1.1.2.1 ht,?_⟩
    apply (F.mem_cut_iff_physical hgi j.1.1 ht).mp
    cases b
    · exact mem_iUnion.mpr ⟨i₀ j,(hzero j _).mpr rfl⟩
    · exact mem_iUnion.mpr ⟨i₁ j,(hone j _).mpr rfl⟩
  let π : C((⋃ j, prismEnds (C j)), (K.space ∩ g ⁻¹' S : Set E)) :=
    ⟨fun x => ⟨r x,hraw (himage.subset (mem_image_of_mem r x.property))⟩,
      hrend.continuousOn.domRestrict.subtype_mk _⟩
  have hfinite := finite_fiber_of_prism_cell_maps H C r hrval
  refine ⟨r,hr,hrend,hrval,himage,hraw,hfinite,π,fun _ => rfl,?_,?_⟩
  · intro j a b
    exact hrval j _
  · intro y
    have hinj : InjOn (Subtype.val : (⋃ j, prismEnds (C j) : Set E) → E) (π ⁻¹' {y}) :=
      Subtype.val_injective.injOn
    refine (hfinite (y : E)).1.of_injOn ?_ hinj
    intro x hx
    refine ⟨?_,?_⟩
    · obtain ⟨j,hj⟩ := mem_iUnion.mp x.property
      exact mem_iUnion.mpr ⟨j,prismEnds_subset (C j) hj⟩
    · change π x = y at hx
      exact congrArg Subtype.val hx

end PoincareConjecture.M76.PrismBelt
