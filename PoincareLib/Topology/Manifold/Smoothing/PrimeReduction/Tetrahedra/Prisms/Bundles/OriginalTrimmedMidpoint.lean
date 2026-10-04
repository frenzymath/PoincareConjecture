import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Tetrahedra.Prisms.Bundles.OriginalCutBallMidpointAgreement
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Tetrahedra.Prisms.Bundles.OriginalTrimmedPartitionReflection
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Tetrahedra.Prisms.OriginalTetrahedralCutFamily
import Mathlib.Topology.LocallyFinite

/-! # The continuous physical midpoint retraction on the original trimmed carrier -/

set_option autoImplicit false
open Set Geometry
namespace PoincareMT.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1
local notation "Square" => (I ×ˢ I : Set (ℝ × ℝ))

set_option maxHeartbeats 600000 in
theorem exists_original_trimmed_midpoint
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
    (havoid : Disjoint (⋃ j, prismTrim (H j)) (g ⁻¹' S))
    (J : (⋃ j, prismTrim (H j)) ≃ₜ (⋃ j, prismTrim (H j)))
    (hJvalue : ∀ j (x : prismTrim (H j)),
      (J ⟨x,mem_iUnion.mpr ⟨j,x.property⟩⟩ : E) = prismFiberReflection (C j) x) :
    ∃ m : C((⋃ j, prismTrim (H j)), (⋃ j, prismTrim (H j))),
      (∀ j (x : prismTrim (H j)),
        (m ⟨x,mem_iUnion.mpr ⟨j,x.property⟩⟩ : E) = prismFiberMidpoint (C j) x) ∧
      (∀ x, J (m x) = m x) ∧
      (∀ x, J x = x → m x = x) ∧
      (∀ x, m (m x) = m x) ∧
      ∀ x, m (J x) = m x := by
  classical
  let Cell := RegularOriginalCutCell K g S D F.BallIndex F.ball
  let U := ⋃ j, prismTrim (H j)
  letI : Finite (K.FaceOfCard 4) := K.finite_faceOfCard hK 4
  letI (t : K.FaceOfCard 4) : Finite (F.BallIndex t) := F.finite_ball t
  letI : Finite Cell := by dsimp [Cell,RegularOriginalCutCell]; infer_instance
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
  have hagree (j l : Cell) (x : E) (hj : x ∈ prismTrim (H j)) (hl : x ∈ prismTrim (H l)) :
      (prismFiberMidpoint (C j) ⟨x,hj⟩ : E) = prismFiberMidpoint (C l) ⟨x,hl⟩ := by
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
      have hmid := original_cut_ball_prism_midpoints_agree K g hgi D G hW hZ hL haffine
        (fun b => (p b).1.1.1) (fun b => (p b).1.1.2.1) (fun b => (p b).1.1.2.2) htet
        (fun b => F.cut (p b).1.1 (i₀ (p b))) (fun b => F.ball (p b).1.1 (p b).1.2)
        (fun b => (F.ball_pair (p b).1.1 (p b).1.2).isCompact.isClosed)
        (fun b => hBsub (p b).1.1 (p b).1.2) (fun b => hcomp (p b).1.1 (p b).1.2)
        (fun b => (p b).2) (fun b => H (p b)) (fun b => flip (p b))
        (fun b => hformula (p b)) ⟨hxj,hxl⟩ hxS
      exact (prismFiberMidpoint_trim_chart (H j) (C j) (hCv j) ⟨x,hj⟩).trans
        (hmid.trans (prismFiberMidpoint_trim_chart (H l) (C l) (hCv l) ⟨x,hl⟩).symm)
  have hclosed (j : Cell) : IsClosed (prismTrim (H j)) := by
    letI : CompactSpace (F.cut j.1.1 (i₀ j) ×ˢ I : Set (E × ℝ)) :=
      isCompact_iff_compactSpace.mp ((F.disk_pair j.1.1 (i₀ j)).isCompact.prod isCompact_Icc)
    letI : CompactSpace (prismTrim (H j)) := (C j).compactSpace
    exact (isCompact_iff_compactSpace.mpr inferInstance).isClosed
  let pieces (j : Cell) : Set U := {x | (x : E) ∈ prismTrim (H j)}
  let maps (j : Cell) : C(pieces j,U) :=
    ⟨fun x => ⟨prismFiberMidpoint (C j) ⟨x.1,x.2⟩,
      mem_iUnion.mpr ⟨j,(prismFiberMidpoint (C j) ⟨x.1,x.2⟩).property⟩⟩,by
      exact (continuous_subtype_val.comp ((continuous_prismFiberMidpoint (C j)).comp
        ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _))).subtype_mk _⟩
  have hmaps (j l : Cell) (x : U) (hj : x ∈ pieces j) (hl : x ∈ pieces l) :
      maps j ⟨x,hj⟩ = maps l ⟨x,hl⟩ := Subtype.ext (hagree j l x hj hl)
  have hcover : ⋃ j, pieces j = univ := by
    apply iUnion_eq_univ_iff.mpr
    intro x
    change ∃ j, (x : E) ∈ prismTrim (H j)
    exact mem_iUnion.mp x.property
  let m := Set.liftCover pieces (fun j => maps j) hmaps hcover
  have hval (j : Cell) (x : pieces j) : m x = maps j x := Set.liftCover_coe x
  have hm : Continuous m := by
    apply (locallyFinite_of_finite pieces).continuous hcover
    · intro j
      exact (hclosed j).preimage continuous_subtype_val
    · intro j
      rw [continuousOn_iff_continuous_domRestrict]
      have he : (pieces j).domRestrict m = maps j := funext (hval j)
      rw [he]
      exact (maps j).continuous
  have hvalue (j : Cell) (x : prismTrim (H j)) :
      (m ⟨x,mem_iUnion.mpr ⟨j,x.property⟩⟩ : E) = prismFiberMidpoint (C j) x :=
    congrArg Subtype.val (hval j ⟨⟨x,mem_iUnion.mpr ⟨j,x.property⟩⟩,x.property⟩)
  have hfixed (x : U) : J (m x) = m x := by
    obtain ⟨j,hxj⟩ := mem_iUnion.mp x.property
    have he : m x = ⟨prismFiberMidpoint (C j) ⟨x,hxj⟩,
        mem_iUnion.mpr ⟨j,(prismFiberMidpoint (C j) ⟨x,hxj⟩).property⟩⟩ :=
      Subtype.ext (hvalue j ⟨x,hxj⟩)
    apply Subtype.ext
    rw [he,hJvalue,prismFiberMidpoint_fixed]
  have hfixes (x : U) (hx : J x = x) : m x = x := by
    obtain ⟨j,hxj⟩ := mem_iUnion.mp x.property
    have he : prismFiberReflection (C j) ⟨x,hxj⟩ = ⟨x,hxj⟩ :=
      Subtype.ext ((hJvalue j ⟨x,hxj⟩).symm.trans (congrArg Subtype.val hx))
    exact Subtype.ext ((hvalue j ⟨x,hxj⟩).trans
      (congrArg Subtype.val ((prismFiberMidpoint_eq_self_iff (C j) _).mpr he)))
  refine ⟨⟨m,hm⟩,hvalue,hfixed,hfixes,fun x => hfixes (m x) (hfixed x),?_⟩
  intro x
  obtain ⟨j,hxj⟩ := mem_iUnion.mp x.property
  have he : J x = ⟨prismFiberReflection (C j) ⟨x,hxj⟩,
      mem_iUnion.mpr ⟨j,(prismFiberReflection (C j) ⟨x,hxj⟩).property⟩⟩ :=
    Subtype.ext (hJvalue j ⟨x,hxj⟩)
  apply Subtype.ext
  change (m (J x) : E) = m x
  rw [he,hvalue,prismFiberMidpoint_reflection]
  exact (hvalue j ⟨x,hxj⟩).symm

end PoincareMT.M76.PrismBelt
