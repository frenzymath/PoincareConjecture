import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Tetrahedra.Prisms.Gluing.GlobalOriginalPrismFamily
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Tetrahedra.Prisms.OriginalDiskCutRectangleSuccessor
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Counting.OriginalExceptionalComponents

/-!
# Globally compatible prisms from the original normalized sphere pieces

Original face position constructs one rectangle family and one set of
fiber charts on the entire finite model. Every disk-normalized tetrahedron
then constructs its actual cut-ball partition and simultaneously marked
whole products, using those same face charts.
-/

set_option autoImplicit false
universe v
open Set Geometry
namespace PoincareMT.M76.PrismBelt
local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1
local notation "Square" => (I ×ˢ I : Set (ℝ × ℝ))

theorem exists_global_original_disk_cut_prisms
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (g : E → X) (hgi : InjOn g K.space)
    (Q : K.FaceOfCard 3 → OpenPartialHomeomorph X V3)
    (A : K.FaceOfCard 3 → E →ᴬ[ℝ] V3)
    (hmap : ∀ s, MapsTo g (convexHull ℝ (s.1 : Set E)) (Q s).source)
    (hA : ∀ s, EqOn ((Q s) ∘ g) (A s) (convexHull ℝ (s.1 : Set E)))
    {S : Set X} (havoid : Disjoint S (g '' K.vertices))
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
      ∀ (ι : Type v) [Finite ι],
      ∀ {t : Finset E} (ht : t ∈ K.faces) (ht4 : t.card = 4),
      let Dₜ := fun f : TetrahedronFace K t => D f.1
      ∀
    (cut rim : ι → Set E) (hcut : ∀ i, IsFinitePLBallPair (ℝ × ℝ) (cut i) (rim i))
    (hsub : ∀ i, cut i ⊆ convexHull ℝ (t : Set E))
    (hrim : ∀ i, cut i ∩ intrinsicFrontier ℝ (convexHull ℝ (t : Set E)) = rim i)
    (hdis : Pairwise fun i j => Disjoint (cut i) (cut j))
    (hphysical : g '' (⋃ i, cut i) = S ∩ (g '' convexHull ℝ (t : Set E))),
      ∃ (κ : Type) (_ : Finite κ) (B R : κ → Set E) (ends : ι → Bool → κ),
      Nat.card κ = Nat.card ι + 1 ∧
      (∀ k, IsFinitePLBallPair V3 (B k) (R k)) ∧
      (∀ k, R k = B k ∩ (intrinsicFrontier ℝ (convexHull ℝ (t : Set E)) ∪ ⋃ i, cut i)) ∧
      (⋃ k, B k) = convexHull ℝ (t : Set E) ∧
      Pairwise (fun k l => B k ∩ B l ⊆ ⋃ i, cut i) ∧
      (∀ i, ends i false ≠ ends i true) ∧
      (∀ i k, ((k = ends i false ∨ k = ends i true) → B k ∩ cut i = cut i) ∧
        (k ≠ ends i false → k ≠ ends i true → Disjoint (B k) (cut i))) ∧
      (∀ k x, x ∈ B k \ ⋃ i, cut i →
        connectedComponentIn (convexHull ℝ (t : Set E) \ ⋃ i, cut i) x = B k \ ⋃ i, cut i) ∧
      ∀ k (x : (K.space \ g ⁻¹' S : Set E)), (x : E) ∈ B k →
        ConnectedComponents.mk x ∉ bad →
    ∃ i₀ i₁ : ι, i₀ ≠ i₁ ∧ cut i₀ ⊆ R k ∧ cut i₁ ⊆ R k ∧
      ∃ flip : CutBallRectangle Dₜ (B k) → Bool,
      ∃ H : (cut i₀ ×ˢ I : Set (E × ℝ)) ≃ₜ B k, H.IsFinitePL ∧
        (∀ (x : E) (hx : x ∈ cut i₀), (H ⟨(x,0),hx,le_rfl,zero_le_one⟩ : E) = x) ∧
        (∀ x, (H x : E) ∈ cut i₀ ↔ (x : E × ℝ).2 = 0) ∧
        (∀ x, (H x : E) ∈ cut i₁ ↔ (x : E × ℝ).2 = 1) ∧
        (∀ z x, (H x : E) ∈ (Dₜ z.1.1).carrier z.1.2 ↔
          (x : E × ℝ).1 ∈ (Dₜ z.1.1).arc ((Dₜ z.1.1).cap z.1.2 (flip z))) ∧
        ∀ (z : CutBallRectangle Dₜ (B k)) (u t : I),
          (H.symm ⟨G z.1.1.1 z.1.2 ⟨(u,fiberFlip (flip z) t),u.property,(fiberFlip (flip z) t).property⟩,
            z.2 (G z.1.1.1 z.1.2 _).property⟩ : E × ℝ) =
            ((G z.1.1.1 z.1.2 ⟨(u,fiberFlip (flip z) 0),u.property,(fiberFlip (flip z) 0).property⟩ : E),(t : ℝ)) := by
  classical
  let D (s : K.FaceOfCard 3) : OriginalFaceRectangles K g S s.1 :=
    Classical.choice (exists_original_face_rectangles K g hgi s.2.1 s.2.2
      (Q s) (A s) (hmap s) (hA s) havoid (hposition s))
  obtain ⟨G,hG,hW,hZ,hL,hside,hprisms⟩ := exists_global_original_prism_family K hK g hgi D
  obtain ⟨bad,hbad,hbadBound,hbadCover,_⟩ :=
    exists_original_exceptional_component_bound K hK g hgi S D
  refine ⟨D,bad,hbad,hbadBound,hbadCover,G,hG,hW,hZ,hL,hside,?_⟩
  intro ι hι t ht ht4
  dsimp only
  intro cut rim hcut hsub hrim hdis hphysical
  obtain ⟨κ,hκ,B,R,ends,hcount,hB,hR,hcover,hinter,hends,hinc,_,_,hcomp,_⟩ :=
    exists_marked_disk_cut_ball_partition
      (isFinitePLBallPair_independent_tetrahedron t (K.indep ht) ht4)
      cut rim hcut hsub hrim hdis
  have hphysical' (x : E) (hx : x ∈ convexHull ℝ (t : Set E)) :
      x ∈ (⋃ i, cut i) ↔ g x ∈ S :=
    original_face_cut_mem_iff K g hgi ht (iUnion_subset hsub) hphysical hx
  have hglobal : (convexHull ℝ (t : Set E) \ g ⁻¹' S : Set E) =
      convexHull ℝ (t : Set E) \ ⋃ i, cut i := by
    ext x
    exact and_congr_right (fun hx => not_congr (hphysical' x hx).symm)
  have hlocal (k : κ) : (B k \ g ⁻¹' S : Set E) = B k \ ⋃ i, cut i := by
    ext x
    exact and_congr_right (fun hx => not_congr
      (hphysical' x (hcover.subset (mem_iUnion.mpr ⟨k,hx⟩))).symm)
  have hcomp' (k : κ) (x : E) (hx : x ∈ B k \ g ⁻¹' S) :
      connectedComponentIn (convexHull ℝ (t : Set E) \ g ⁻¹' S) x = B k \ g ⁻¹' S := by
    rw [hglobal,hlocal]
    exact hcomp k x ((hlocal k).subset hx)
  have hwhole (k : κ) (i : ι) (hmeet : (B k ∩ cut i).Nonempty) : cut i ⊆ R k := by
    have hi : k = ends i false ∨ k = ends i true := by
      by_contra hne
      obtain ⟨x,hxB,hxC⟩ := hmeet
      exact disjoint_left.mp ((hinc i k).2 (fun h => hne (Or.inl h))
        (fun h => hne (Or.inr h))) hxB hxC
    intro x hx
    exact (hR k).symm.subset ⟨((hinc i k).1 hi).symm.subset hx |>.1,
      Or.inr (mem_iUnion.mpr ⟨i,hx⟩)⟩
  refine ⟨κ,hκ,B,R,ends,hcount,hB,hR,hcover,hinter,hends,hinc,hcomp,?_⟩
  intro k x hxB hxgood
  have hregular (f : TetrahedronFace K t)
      (y : (convexHull ℝ (f.1.1 : Set E) \ ⋃ i, (D f.1).arc i : Set E))
      (hyB : (y : E) ∈ B k) : ConnectedComponents.mk y ∉ (D f.1).exceptional := by
    intro hybad
    have hyGlobal := (D f.1).cut_subset_original_complement f.1.2.1 hgi y.property
    have hclass := original_cut_ball_component_class K g ht
      (fun z hz => hcover.subset (mem_iUnion.mpr ⟨k,hz⟩)) (hcomp' k)
      (show (x : E) ∈ B k \ g ⁻¹' S from ⟨hxB,x.property.2⟩)
      (show (y : E) ∈ B k \ g ⁻¹' S from ⟨hyB,hyGlobal.2⟩)
    exact hxgood (hclass ▸ hbadCover f.1 y hybad)
  exact hprisms ι ht ht4 cut rim hcut hsub hrim hdis hphysical
    (hB k) (hR k) (hwhole k) (hcomp' k) hregular

end PoincareMT.M76.PrismBelt
