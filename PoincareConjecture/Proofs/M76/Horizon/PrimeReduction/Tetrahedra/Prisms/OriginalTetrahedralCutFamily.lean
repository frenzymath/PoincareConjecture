import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.MarkedDiskIncidence
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.OriginalTetrahedronBall
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteFaceCounts









set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt
universe u
local notation "V3" => (Fin 3 → ℝ)

structure OriginalTetrahedralCutFamily
    {E : Type u} {X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [DecidableEq E] (K : SimplicialComplex ℝ E) (g : E → X) (S : Set X) where
  DiskIndex : K.FaceOfCard 4 → Type u
  finite_disk : ∀ t, Finite (DiskIndex t)
  cut : ∀ t, DiskIndex t → Set E
  rim : ∀ t, DiskIndex t → Set E
  disk_pair : ∀ t i, IsFinitePLBallPair (ℝ × ℝ) (cut t i) (rim t i)
  disk_subset : ∀ t i, cut t i ⊆ convexHull ℝ (t.1 : Set E)
  disk_frontier : ∀ t i,
    cut t i ∩ intrinsicFrontier ℝ (convexHull ℝ (t.1 : Set E)) = rim t i
  disk_disjoint : ∀ t, Pairwise fun i j => Disjoint (cut t i) (cut t j)
  physical : ∀ t, g '' (⋃ i, cut t i) = S ∩ (g '' convexHull ℝ (t.1 : Set E))
  BallIndex : K.FaceOfCard 4 → Type
  finite_ball : ∀ t, Finite (BallIndex t)
  ball : ∀ t, BallIndex t → Set E
  boundary : ∀ t, BallIndex t → Set E
  ends : ∀ t, DiskIndex t → Bool → BallIndex t
  card_ball : ∀ t, Nat.card (BallIndex t) = Nat.card (DiskIndex t) + 1
  ball_pair : ∀ t k, IsFinitePLBallPair V3 (ball t k) (boundary t k)
  ball_frontier : ∀ t k, boundary t k = ball t k ∩
    (intrinsicFrontier ℝ (convexHull ℝ (t.1 : Set E)) ∪ ⋃ i, cut t i)
  cover : ∀ t, (⋃ k, ball t k) = convexHull ℝ (t.1 : Set E)
  intersection : ∀ t, Pairwise fun k l => ball t k ∩ ball t l ⊆ ⋃ i, cut t i
  ends_ne : ∀ t i, ends t i false ≠ ends t i true
  incidence : ∀ t i k,
    ((k = ends t i false ∨ k = ends t i true) → ball t k ∩ cut t i = cut t i) ∧
    (k ≠ ends t i false → k ≠ ends t i true → Disjoint (ball t k) (cut t i))
  component : ∀ t k x, x ∈ ball t k \ ⋃ i, cut t i →
    connectedComponentIn (convexHull ℝ (t.1 : Set E) \ ⋃ i, cut t i) x =
      ball t k \ ⋃ i, cut t i
  closure_component : ∀ t k, closure (ball t k \ ⋃ i, cut t i) = ball t k

theorem exists_original_tetrahedral_cut_family
    {E : Type u} {X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E]
    (K : SimplicialComplex ℝ E) (g : E → X) (S : Set X)
    (hdisks : ∀ t ∈ K.faces, t.card = 4 →
      ∃ γ : Type u, Finite γ ∧ ∃ cut rim : γ → Set E,
        (∀ j, IsFinitePLBallPair (ℝ × ℝ) (cut j) (rim j)) ∧
        (∀ j, cut j ⊆ convexHull ℝ (t : Set E)) ∧
        (∀ j, cut j ∩ intrinsicFrontier ℝ (convexHull ℝ (t : Set E)) = rim j) ∧
        Pairwise (fun j k => Disjoint (cut j) (cut k)) ∧
        g '' (⋃ j, cut j) = S ∩ (g '' convexHull ℝ (t : Set E))) :
    Nonempty (OriginalTetrahedralCutFamily K g S) := by
  classical
  choose ι hι cut rim hcut hsub hrim hdis hphysical using
    fun t : K.FaceOfCard 4 => hdisks t.1 t.2.1 t.2.2
  letI (t : K.FaceOfCard 4) : Finite (ι t) := hι t
  have hpart (t : K.FaceOfCard 4) := exists_marked_disk_cut_ball_partition
    (isFinitePLBallPair_independent_tetrahedron t.1 (K.indep t.2.1) t.2.2)
    (cut t) (rim t) (hcut t) (hsub t) (hrim t) (hdis t)
  choose κ hκ B R ends hcard hB hR hcover hinter hends hinc hfront hcap hcomp hclosure
    using hpart
  exact ⟨⟨ι,hι,cut,rim,hcut,hsub,hrim,hdis,hphysical,
    κ,hκ,B,R,ends,hcard,hB,hR,hcover,hinter,hends,hinc,hcomp,hclosure⟩⟩

theorem OriginalTetrahedralCutFamily.whole_disk
    {E : Type u} {X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [DecidableEq E] {K : SimplicialComplex ℝ E} {g : E → X} {S : Set X}
    (F : OriginalTetrahedralCutFamily K g S) (t : K.FaceOfCard 4)
    (k : F.BallIndex t) (i : F.DiskIndex t)
    (hmeet : (F.ball t k ∩ F.cut t i).Nonempty) : F.cut t i ⊆ F.boundary t k := by
  have hi : k = F.ends t i false ∨ k = F.ends t i true := by
    by_contra hne
    obtain ⟨x,hxB,hxD⟩ := hmeet
    exact disjoint_left.mp ((F.incidence t i k).2 (fun h => hne (Or.inl h))
      (fun h => hne (Or.inr h))) hxB hxD
  intro x hx
  exact (F.ball_frontier t k).symm.subset
    ⟨((F.incidence t i k).1 hi).symm.subset hx |>.1,Or.inr (mem_iUnion.mpr ⟨i,hx⟩)⟩

end PoincareConjecture.M76.PrismBelt
