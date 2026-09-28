import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.OriginalCutBallInterpolation
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.OriginalCutBallMidpointAgreement
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.OriginalTrimmedPartitionReflection
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.OriginalTetrahedralCutFamily
import Mathlib.Topology.LocallyFinite

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1
local notation "Square" => (I ×ˢ I : Set (ℝ × ℝ))

set_option maxHeartbeats 600000 in
theorem original_trimmed_interpolation_agrees
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E]
    (K : SimplicialComplex ℝ E) (g : E → X) (hgi : InjOn g K.space)
    {S : Set X} (D : ∀ s : K.FaceOfCard 3, OriginalFaceRectangles K g S s.1)
    (G : ∀ s k, Square ≃ₜ (D s).carrier k)
    (hW : ∀ s k y, (G s k y : E) ∈ (D s).arc ((D s).cap k false) ↔ (y : ℝ × ℝ).2 = 0)
    (hZ : ∀ s k y, (G s k y : E) ∈ (D s).arc ((D s).cap k true) ↔ (y : ℝ × ℝ).2 = 1)
    (hL : ∀ s k b y, (G s k y : E) ∈ (D s).side k b ↔ (y : ℝ × ℝ).1 = if b then 1 else 0)
    (haffine : ∀ s k b t, (G s k (sidePoint b t) : E) =
      AffineMap.lineMap (G s k (sidePoint b 0) : E) (G s k (sidePoint b 1) : E) (t : ℝ))
    (F : OriginalTetrahedralCutFamily K g S)
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
    (hCv : ∀ j x, (C j x : E) = H j (trimProduct (F.cut j.1.1 (i₀ j)) x))
    (havoid : Disjoint (⋃ j, prismTrim (H j)) (g ⁻¹' S)) :
    ∀ j l (x : E) (hj : x ∈ prismTrim (H j)) (hl : x ∈ prismTrim (H l)) (r : I),
      (prismFiberInterpolation (C j) ⟨x,hj⟩ r : E) =
        prismFiberInterpolation (C l) ⟨x,hl⟩ r := by
  classical
  let Cell := RegularOriginalCutCell K g S D F.BallIndex F.ball
  have hBsub (t : K.FaceOfCard 4) (k : F.BallIndex t) :
      F.ball t k ⊆ convexHull ℝ (t.1 : Set E) :=
    fun _ hx => (F.cover t).subset (mem_iUnion.mpr ⟨k,hx⟩)
  have hphysical (t : K.FaceOfCard 4) (x : E) (hx : x ∈ convexHull ℝ (t.1 : Set E)) :
      x ∈ (⋃ i, F.cut t i) ↔ g x ∈ S :=
    original_face_cut_mem_iff K g hgi t.2.1 (iUnion_subset (F.disk_subset t)) (F.physical t) hx
  have hglobal (t : K.FaceOfCard 4) : (convexHull ℝ (t.1 : Set E) \ g ⁻¹' S : Set E) =
      convexHull ℝ (t.1 : Set E) \ ⋃ i, F.cut t i := by
    ext x
    exact and_congr_right (fun hx => not_congr (hphysical t x hx).symm)
  have hlocal (t : K.FaceOfCard 4) (k : F.BallIndex t) :
      (F.ball t k \ g ⁻¹' S : Set E) = F.ball t k \ ⋃ i, F.cut t i := by
    ext x
    exact and_congr_right (fun hx => not_congr (hphysical t x (hBsub t k hx)).symm)
  have hcomp (t : K.FaceOfCard 4) (k : F.BallIndex t) (x : E)
      (hx : x ∈ F.ball t k \ g ⁻¹' S) :
      connectedComponentIn (convexHull ℝ (t.1 : Set E) \ g ⁻¹' S) x = F.ball t k \ g ⁻¹' S := by
    rw [hglobal,hlocal]
    exact F.component t k x ((hlocal t k).subset hx)
  intro j l x hj hl r
  by_cases hsame : j = l
  · subst l
    rfl
  have hxj := prismTrim_subset (H j) hj
  have hxl := prismTrim_subset (H l) hl
  have hxS : g x ∉ S := fun hx => disjoint_left.mp havoid (mem_iUnion.mpr ⟨j,hj⟩) hx
  by_cases ht : j.1.1 = l.1.1
  · exfalso
    rcases j with ⟨⟨t,k⟩,hjreg⟩
    rcases l with ⟨⟨u,n⟩,hlreg⟩
    dsimp only at ht
    subst u
    have hkn : k ≠ n := fun h => hsame (Subtype.ext (by subst n; rfl))
    exact hxS ((hphysical t x (hBsub t k hxj)).mp ((F.intersection t hkn) ⟨hxj,hxl⟩))
  · let p : Bool → Cell := Bool.rec j l
    have htet : (p false).1.1.1 ≠ (p true).1.1.1 := fun h => ht (Subtype.ext h)
    have hi := original_cut_ball_prism_interpolation_agrees K g hgi D G hW hZ hL haffine
      (fun b => (p b).1.1.1) (fun b => (p b).1.1.2.1) (fun b => (p b).1.1.2.2) htet
      (fun b => F.cut (p b).1.1 (i₀ (p b))) (fun b => F.ball (p b).1.1 (p b).1.2)
      (fun b => (F.ball_pair (p b).1.1 (p b).1.2).isCompact.isClosed)
      (fun b => hBsub (p b).1.1 (p b).1.2) (fun b => hcomp (p b).1.1 (p b).1.2)
      (fun b => (p b).2) (fun b => H (p b)) (fun b => flip (p b))
      (fun b => hformula (p b)) ⟨hxj,hxl⟩ hxS r
    exact (prismFiberInterpolation_trim_chart (H j) (C j) (hCv j) ⟨x,hj⟩ r).trans
      (hi.trans (prismFiberInterpolation_trim_chart (H l) (C l) (hCv l) ⟨x,hl⟩ r).symm)

end PoincareConjecture.M76.PrismBelt
