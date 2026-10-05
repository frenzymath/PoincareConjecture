import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Tetrahedra.Prisms.CutComponentSidePairing
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Tetrahedra.Prisms.MarkedDiskIncidence
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Tetrahedra.OriginalTetrahedronBall

/-!
# The rectangle successor of an original disk-normalized tetrahedron

Starting with the original normal-face position and actual disjoint
proper cutting disks, construct the face regions and complementary
balls together. On every ball avoiding the constructed exceptional
face regions, derive the full-side pairing and finite successor cycles.
Neither the ball partition nor the side incidence is supplied.
-/

set_option autoImplicit false
open Set Geometry
namespace PoincareMT.M76.PrismBelt
local notation "V3" => (Fin 3 → ℝ)

theorem exists_original_disk_cut_rectangle_successor
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X] [Finite ι]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (g : E → X) (hgi : InjOn g K.space)
    (Q : K.FaceOfCard 3 → OpenPartialHomeomorph X V3)
    (A : K.FaceOfCard 3 → E →ᴬ[ℝ] V3)
    (hmap : ∀ s, MapsTo g (convexHull ℝ (s.1 : Set E)) (Q s).source)
    (hA : ∀ s, EqOn ((Q s) ∘ g) (A s) (convexHull ℝ (s.1 : Set E)))
    {S : Set X} (havoid : Disjoint S (g '' K.vertices))
    (hposition : ∀ s, InCircleFreeNonreturningTriangleGraphPosition (Q s) S g s.1 (A s))
    {t : Finset E} (ht : t ∈ K.faces) (ht4 : t.card = 4)
    (cut rim : ι → Set E) (hcut : ∀ i, IsFinitePLBallPair (ℝ × ℝ) (cut i) (rim i))
    (hsub : ∀ i, cut i ⊆ convexHull ℝ (t : Set E))
    (hrim : ∀ i, cut i ∩ intrinsicFrontier ℝ (convexHull ℝ (t : Set E)) = rim i)
    (hdis : Pairwise fun i j => Disjoint (cut i) (cut j))
    (hphysical : g '' (⋃ i, cut i) = S ∩ (g '' convexHull ℝ (t : Set E))) :
    ∃ D : ∀ f : TetrahedronFace K t, OriginalFaceRectangles K g S f.1.1,
      ∃ κ : Type, Finite κ ∧ ∃ (B R : κ → Set E) (ends : ι → Bool → κ),
      Nat.card κ = Nat.card ι + 1 ∧
      (∀ k, IsFinitePLBallPair V3 (B k) (R k)) ∧
      (∀ k, R k = B k ∩ (intrinsicFrontier ℝ (convexHull ℝ (t : Set E)) ∪ ⋃ i, cut i)) ∧
      (⋃ k, B k) = convexHull ℝ (t : Set E) ∧
      (∀ i, ends i false ≠ ends i true) ∧
      (∀ i k, ((k = ends i false ∨ k = ends i true) → B k ∩ cut i = cut i) ∧
        (k ≠ ends i false → k ≠ ends i true → Disjoint (B k) (cut i))) ∧
      (∀ k x, x ∈ B k \ ⋃ i, cut i →
        connectedComponentIn (convexHull ℝ (t : Set E) \ ⋃ i, cut i) x = B k \ ⋃ i, cut i) ∧
      (∀ k, closure (B k \ ⋃ i, cut i) = B k) ∧
      ∀ k, (∀ (f : TetrahedronFace K t)
        (x : (convexHull ℝ (f.1.1 : Set E) \ ⋃ i, (D f).arc i : Set E)),
        (x : E) ∈ B k → ConnectedComponents.mk x ∉ (D f).exceptional) →
      ∃ p next : Equiv.Perm (RectangleSideFlag D (B k)), Function.Involutive p ∧
        (∀ z, (p z).1.1 ≠ z.1.1) ∧ (∀ z, (p z).carrier = z.carrier) ∧
        next = p.trans RectangleSideFlag.switch ∧
        (∀ z, (next z).1.1 ≠ z.1.1) ∧
        ∀ z, ∃ n : ℕ, 0 < n ∧
          (next : RectangleSideFlag D (B k) → RectangleSideFlag D (B k))^[n] z = z ∧
          Function.Injective (fun j : Fin n =>
            (next : RectangleSideFlag D (B k) → RectangleSideFlag D (B k))^[j.val] z) := by
  classical
  let D (f : TetrahedronFace K t) : OriginalFaceRectangles K g S f.1.1 :=
    Classical.choice (exists_original_face_rectangles K g hgi f.1.2.1 f.1.2.2
      (Q f.1) (A f.1) (hmap f.1) (hA f.1) havoid (hposition f.1))
  obtain ⟨κ,hκ,B,R,ends,hcount,hB,hR,hcover,_,hends,hinc,_,_,hcomp,hclosure⟩ :=
    exists_marked_disk_cut_ball_partition
      (isFinitePLBallPair_independent_tetrahedron t (K.indep ht) ht4)
      cut rim hcut hsub hrim hdis
  have hcutSub : (⋃ i, cut i) ⊆ convexHull ℝ (t : Set E) := iUnion_subset hsub
  have hglobal : (convexHull ℝ (t : Set E) \ g ⁻¹' S : Set E) =
      convexHull ℝ (t : Set E) \ ⋃ i, cut i := by
    ext x
    constructor
    · intro hx
      exact ⟨hx.1,fun hc => hx.2 ((hphysical.subset (mem_image_of_mem g hc)).1)⟩
    · intro hx
      exact ⟨hx.1,fun hxS => hx.2
        ((original_face_cut_mem_iff K g hgi ht hcutSub hphysical hx.1).mpr hxS)⟩
  have hlocal (k : κ) : (B k \ g ⁻¹' S : Set E) = B k \ ⋃ i, cut i := by
    ext x
    have hBk : B k ⊆ convexHull ℝ (t : Set E) := fun y hy =>
      hcover.subset (mem_iUnion.mpr ⟨k,hy⟩)
    constructor
    · intro hx
      exact ⟨hx.1,(hglobal.subset ⟨hBk hx.1,hx.2⟩).2⟩
    · intro hx
      exact ⟨hx.1,(hglobal.symm.subset ⟨hBk hx.1,hx.2⟩).2⟩
  refine ⟨D,κ,hκ,B,R,ends,hcount,hB,hR,hcover,hends,hinc,hcomp,hclosure,?_⟩
  intro k hregular
  apply exists_cut_component_rectangle_successor hK hgi ht ht4 D (hB k).isCompact.isClosed
    ?_ hregular
  intro x hx
  rw [hglobal,hlocal k]
  exact hcomp k x ((hlocal k).subset hx)

end PoincareMT.M76.PrismBelt
