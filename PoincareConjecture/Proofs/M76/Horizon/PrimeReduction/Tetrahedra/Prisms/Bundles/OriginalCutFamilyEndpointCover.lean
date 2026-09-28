import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.OriginalPartitionEndpointCover
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.OriginalTetrahedralCutFamily

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt
universe u
local notation "I" => Icc (0 : ℝ) 1
local notation "V3" => (Fin 3 → ℝ)
local notation "Square" => (I ×ˢ I : Set (ℝ × ℝ))

set_option maxHeartbeats 4000000 in
theorem OriginalTetrahedralCutFamily.exists_endpoint_cover
    {E : Type u} {X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]
    {K : SimplicialComplex ℝ E} (hK : K.faces.Finite)
    {g : E → X} (hgi : InjOn g K.space) {S : Set X}
    (F : OriginalTetrahedralCutFamily K g S)
    (Q : K.FaceOfCard 3 → OpenPartialHomeomorph X V3)
    (A : K.FaceOfCard 3 → E →ᴬ[ℝ] V3)
    (hmap : ∀ s, MapsTo g (convexHull ℝ (s.1 : Set E)) (Q s).source)
    (hA : ∀ s, EqOn ((Q s) ∘ g) (A s) (convexHull ℝ (s.1 : Set E)))
    (havoid : Disjoint S (g '' K.vertices))
    (hposition : ∀ s, InCircleFreeNonreturningTriangleGraphPosition (Q s) S g s.1 (A s)) :
    ∃ D : ∀ s : K.FaceOfCard 3, OriginalFaceRectangles K g S s.1,
    ∃ bad : Set (ConnectedComponents (K.space \ g ⁻¹' S : Set E)),
      bad.Finite ∧ bad.ncard ≤ 4 * Nat.card (K.FaceOfCard 3) ∧
      (∀ (s : K.FaceOfCard 3)
        (x : (convexHull ℝ (s.1 : Set E) \ ⋃ i, (D s).arc i : Set E)),
        ConnectedComponents.mk x ∈ (D s).exceptional →
        ConnectedComponents.mk
          (⟨x,(D s).cut_subset_original_complement s.2.1 hgi x.property⟩ :
            (K.space \ g ⁻¹' S : Set E)) ∈ bad) ∧
    ∃ G : ∀ s k, Square ≃ₜ (D s).carrier k,
      (∀ s k, (G s k).IsFinitePL) ∧
      (∀ s k x, (G s k x : E) ∈ (D s).arc ((D s).cap k false) ↔
        (x : ℝ × ℝ).2 = 0) ∧
      (∀ s k x, (G s k x : E) ∈ (D s).arc ((D s).cap k true) ↔
        (x : ℝ × ℝ).2 = 1) ∧
      (∀ s k b x, (G s k x : E) ∈ (D s).side k b ↔
        (x : ℝ × ℝ).1 = if b then 1 else 0) ∧
      (∀ s k b t, (G s k (sidePoint b t) : E) =
        AffineMap.lineMap (G s k (sidePoint b 0) : E)
          (G s k (sidePoint b 1) : E) (t : ℝ)) ∧
    let Cell := RegularOriginalCutCell K g S D F.BallIndex F.ball
    ∃ (i₀ i₁ : ∀ j : Cell, F.DiskIndex j.1.1),
      (∀ j, i₀ j ≠ i₁ j) ∧
      (∀ j, F.cut j.1.1 (i₀ j) ⊆ F.boundary j.1.1 j.1.2 ∧
        F.cut j.1.1 (i₁ j) ⊆ F.boundary j.1.1 j.1.2) ∧
    ∃ flip : ∀ j : Cell,
      CutBallRectangle (fun f : TetrahedronFace K j.1.1.1 => D f.1)
        (F.ball j.1.1 j.1.2) → Bool,
    ∃ H : ∀ j : Cell, (F.cut j.1.1 (i₀ j) ×ˢ I : Set (E × ℝ)) ≃ₜ F.ball j.1.1 j.1.2,
      (∀ j, (H j).IsFinitePL) ∧
      (∀ j x, (H j x : E) ∈ F.cut j.1.1 (i₀ j) ↔ (x : E × ℝ).2 = 0) ∧
      (∀ j x, (H j x : E) ∈ F.cut j.1.1 (i₁ j) ↔ (x : E × ℝ).2 = 1) ∧
      (∀ j (z : CutBallRectangle (fun f : TetrahedronFace K j.1.1.1 => D f.1)
        (F.ball j.1.1 j.1.2)) (u t : I),
        ((H j).symm ⟨G z.1.1.1 z.1.2
          ⟨(u,fiberFlip (flip j z) t),u.property,(fiberFlip (flip j z) t).property⟩,
          z.2 (G _ _ _).property⟩ : E × ℝ) =
          ((G z.1.1.1 z.1.2
            ⟨(u,fiberFlip (flip j z) 0),u.property,(fiberFlip (flip j z) 0).property⟩ : E),(t : ℝ))) ∧
    ∃ C : ∀ j : Cell, (F.cut j.1.1 (i₀ j) ×ˢ I : Set (E × ℝ)) ≃ₜ prismTrim (H j),
      (∀ j, (C j).IsFinitePL) ∧
      (∀ j x, (C j x : E) = H j (trimProduct (F.cut j.1.1 (i₀ j)) x)) ∧
      Disjoint (⋃ j, prismTrim (H j)) (g ⁻¹' S) ∧
    ∃ (J : (⋃ j, prismTrim (H j)) ≃ₜ (⋃ j, prismTrim (H j))),
      J.IsFinitePL ∧ Function.Involutive J ∧
      (∀ j (x : prismTrim (H j)),
        (J ⟨x,mem_iUnion.mpr ⟨j,x.property⟩⟩ : E) = prismFiberReflection (C j) x) ∧
    ∃ (τ : (⋃ j, prismEnds (C j)) ≃ₜ (⋃ j, prismEnds (C j)))
      (hτ : Function.Involutive τ),
      (∀ x, τ x ≠ x) ∧
      (∀ x, (τ x : E) = J ⟨x,by
        obtain ⟨j,hj⟩ := mem_iUnion.mp x.property
        exact mem_iUnion.mpr ⟨j,prismEnds_subset (C j) hj⟩⟩) ∧
      (∀ j (x : F.cut j.1.1 (i₀ j)) (b : Bool),
        (τ (prismEndpointLift C j x b) : E) = prismEndMap (C j) x (!b)) ∧
      IsCoveringMap (FreeInvolutionQuotient.projection τ hτ) ∧
      (∀ x, FreeInvolutionQuotient.projection τ hτ ⁻¹'
        {FreeInvolutionQuotient.projection τ hτ x} = {x,τ x}) ∧
      let q := FreeInvolutionQuotient.projection τ hτ
      let m := fun j (x : F.cut j.1.1 (i₀ j)) => q (prismEndpointLift C j x false)
      (∀ j, ∃ Gcap : F.cut j.1.1 (i₀ j) ≃ₜ range (m j),
        ∀ x, (Gcap x : FreeInvolutionQuotient.Model τ hτ) = m j x) ∧
      (∀ j x, q (prismEndpointLift C j x true) = m j x) ∧
      (⋃ j, range (m j)) = univ := by
  classical
  let (t : K.FaceOfCard 4) : Finite (F.DiskIndex t) := F.finite_disk t
  let (t : K.FaceOfCard 4) : Finite (F.BallIndex t) := F.finite_ball t
  let D (s : K.FaceOfCard 3) : OriginalFaceRectangles K g S s.1 :=
    Classical.choice (exists_original_face_rectangles K g hgi s.2.1 s.2.2
      (Q s) (A s) (hmap s) (hA s) havoid (hposition s))
  obtain ⟨G,hG,hW,hZ,hL,hside,_⟩ := exists_global_original_prism_family.{u,u,_} K hK g hgi D
  obtain ⟨bad,hbad,hbound,hbadCover,_⟩ :=
    exists_original_exceptional_component_bound K hK g hgi S D
  refine ⟨D,bad,hbad,hbound,hbadCover,G,hG,hW,hZ,hL,hside,?_⟩
  exact exists_original_partition_endpoint_cover K hK g hgi D G hG hW hZ hL hside
    F.DiskIndex F.BallIndex F.cut F.rim F.disk_pair F.disk_subset F.disk_frontier
    F.disk_disjoint F.physical F.ball F.boundary F.ball_pair F.ball_frontier
    F.cover F.intersection F.whole_disk F.component

end PoincareConjecture.M76.PrismBelt
