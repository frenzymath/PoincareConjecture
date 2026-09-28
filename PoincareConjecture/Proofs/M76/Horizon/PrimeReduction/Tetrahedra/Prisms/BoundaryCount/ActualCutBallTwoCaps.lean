import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.BoundaryCount.TwoCapCount
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.BoundaryCount.RectangleContactValence
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervals

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt

theorem actual_cut_ball_has_two_caps
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
    {B R : Set E} (hB : IsFinitePLBallPair (Fin 3 → ℝ) B R)
    (hR : R = B ∩ (intrinsicFrontier ℝ (convexHull ℝ (t : Set E)) ∪ ⋃ i, cut i))
    (hwhole : ∀ i, (B ∩ cut i).Nonempty → cut i ⊆ R)
    (hcomp : ∀ x ∈ B \ g ⁻¹' S,
      connectedComponentIn (convexHull ℝ (t : Set E) \ g ⁻¹' S) x = B \ g ⁻¹' S)
    (hregular : ∀ (f : TetrahedronFace K t)
      (x : (convexHull ℝ (f.1.1 : Set E) \ ⋃ i, (D f).arc i : Set E)),
      (x : E) ∈ B → ConnectedComponents.mk x ∉ (D f).exceptional) :
    Nat.card {i // cut i ⊆ R} = 2 := by
  classical
  let := K.finite_faceOfCard hK 3
  have hval := actual_cut_rectangle_contact_valence hgi ht ht4 D cut rim hcut hsub hrim
    hdis hphysical hB hR hwhole hcomp hregular
  let M (z : CutBallRectangle D B) := (D z.1.1).carrier z.1.2
  let L (z : CutBallRectangle D B) (b : Bool) := (D z.1.1).side z.1.2 b
  let r (z : CutBallRectangle D B) :=
    ((D z.1.1).arc ((D z.1.1).cap z.1.2 false) ∪
      (D z.1.1).arc ((D z.1.1).cap z.1.2 true)) ∪ (L z false ∪ L z true)
  let q (z : CutBallRectangle D B) (b : Bool) : Set E :=
    {(D z.1.1).edge z.1.2 b ((D z.1.1).lo z.1.2 b),
      (D z.1.1).edge z.1.2 b ((D z.1.1).hi z.1.2 b)}
  have hL (z : CutBallRectangle D B) (b : Bool) : IsFinitePLBallPair ℝ (L z b) (q z b) := by
    obtain ⟨hi,_,_,_,_,_,hlt,_⟩ := (D z.1.1).edgeData z.1.2 b
    exact isFinitePLBallPair_affine_interval hlt ((D z.1.1).edge z.1.2 b) hi.injOn
  have hphysical' (x : E) (hx : x ∈ convexHull ℝ (t : Set E)) :
      x ∈ (⋃ i, cut i) ↔ g x ∈ S :=
    original_face_cut_mem_iff K g hgi ht (iUnion_subset hsub) hphysical hx
  have hcover := cut_ball_boundary_eq_disks_union_rectangles hgi ht ht4 D
    hB.isCompact.isClosed hcomp hR hphysical' hregular
  have hinc : B ∩ (⋃ i, cut i) = ⋃ i : {i // cut i ⊆ R}, cut i := by
    ext x
    constructor
    · rintro ⟨hxB,hxc⟩
      obtain ⟨i,hi⟩ := mem_iUnion.mp hxc
      exact mem_iUnion.mpr ⟨⟨i,hwhole i ⟨x,hxB,hi⟩⟩,hi⟩
    · intro hx
      obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      exact ⟨hB.1 (i.2 hi),mem_iUnion.mpr ⟨i,hi⟩⟩
  rw [hinc] at hcover
  have hcapContact (i : {i // cut i ⊆ R}) : cut i ∩ (⋃ z : CutBallRectangle D B, M z) ⊆ rim i := by
    rintro x ⟨hxi,hxM⟩
    obtain ⟨z,hz⟩ := mem_iUnion.mp hxM
    apply (hrim i).subset
    refine ⟨hxi,?_⟩
    have hface : convexHull ℝ (z.1.1.1.1 : Set E) ⊆
        intrinsicFrontier ℝ (convexHull ℝ (t : Set E)) := by
      apply (K.indep ht).convexHull_subset_intrinsicFrontier
      refine Finset.ssubset_iff_subset_ne.mpr ⟨z.1.1.2,?_⟩
      intro he
      have hc := congrArg Finset.card he
      rw [z.1.1.1.2.2,ht4] at hc
      omega
    exact hface ((D z.1.1).carrier_subset_face z.1.2 hz)
  exact two_caps_of_actual_rectangular_boundary_cover K ht ht4 hB
    (fun i : {i // cut i ⊆ R} => cut i) (fun i => rim i) (fun i => hcut i)
    (fun i j hij => hdis (fun he => hij (Subtype.ext he))) M r
    (fun z => (D z.1.1).regionBall z.1.2) L q hL
    (fun z b => (D z.1.1).side_subset_carrier z.1.2 b)
    (fun z => (D z.1.1).sides_disjoint z.1.2) hval.1 hval.2 hcover hcapContact

end PoincareConjecture.M76.PrismBelt
