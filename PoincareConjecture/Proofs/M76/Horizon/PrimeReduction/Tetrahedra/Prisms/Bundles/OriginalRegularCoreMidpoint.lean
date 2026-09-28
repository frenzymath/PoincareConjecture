import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.OriginalRegularComponentCoverage
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.OriginalCutBallMidpointAgreement
import Mathlib.Topology.LocallyFinite



set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1
local notation "Square" => (I ×ˢ I : Set (ℝ × ℝ))

theorem prismFiberMidpoint_mem_trim
    {E : Type*} [TopologicalSpace E] {A B : Set E}
    (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B) (x : B) :
    (prismFiberMidpoint H x : E) ∈ prismTrim H := by
  refine ⟨⟨((H.symm x : E × ℝ).1,fiberMidHeight),
    (H.symm x).property.1,fiberMidHeight.property⟩,?_⟩
  change (H (trimProduct A _) : E) = H _
  congr 2
  apply Subtype.ext
  apply Prod.ext
  · rfl
  change 1/4+(1/2 : ℝ)/2 = 1/2
  norm_num

set_option maxHeartbeats 600000 in
theorem exists_original_regular_core_midpoint
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
          ⟨(u,fiberFlip (flip j z) 0),u.property,(fiberFlip (flip j z) 0).property⟩ : E),(t : ℝ))) :
    ∃ m : C((⋃ j : RegularOriginalCutCell K g S D F.BallIndex F.ball,
        F.ball j.1.1 j.1.2 \ g ⁻¹' S), (⋃ j, prismTrim (H j))),
      ∀ j (x : (F.ball j.1.1 j.1.2 \ g ⁻¹' S : Set E)),
        (m ⟨x,mem_iUnion.mpr ⟨j,x.property⟩⟩ : E) =
          prismFiberMidpoint (H j) ⟨x,x.property.1⟩ := by
  classical
  let Cell := RegularOriginalCutCell K g S D F.BallIndex F.ball
  let U := ⋃ j : Cell, F.ball j.1.1 j.1.2 \ g ⁻¹' S
  let T := ⋃ j : Cell, prismTrim (H j)
  letI : Finite (K.FaceOfCard 4) := K.finite_faceOfCard hK 4
  letI (t : K.FaceOfCard 4) : Finite (F.BallIndex t) := F.finite_ball t
  letI : Finite Cell := by dsimp [Cell,RegularOriginalCutCell]; infer_instance
  have hagree (j l : Cell) (x : E) (hj : x ∈ F.ball j.1.1 j.1.2)
      (hl : x ∈ F.ball l.1.1 l.1.2) (hxS : g x ∉ S) :
      (prismFiberMidpoint (H j) ⟨x,hj⟩ : E) = prismFiberMidpoint (H l) ⟨x,hl⟩ := by
    by_cases hsame : j = l
    · subst l
      rfl
    by_cases ht : j.1.1 = l.1.1
    · exfalso
      rcases j with ⟨⟨t,k⟩,hjreg⟩
      rcases l with ⟨⟨u,n⟩,hlreg⟩
      dsimp only at ht
      subst u
      have hkn : k ≠ n := fun h => hsame (Subtype.ext (by subst n; rfl))
      exact hxS ((F.mem_cut_iff_physical hgi t (F.ball_subset_tetrahedron t k hj)).mp
        ((F.intersection t hkn) ⟨hj,hl⟩))
    · let p : Bool → Cell := Bool.rec j l
      have htet : (p false).1.1.1 ≠ (p true).1.1.1 := fun h => ht (Subtype.ext h)
      exact original_cut_ball_prism_midpoints_agree K g hgi D G hW hZ hL haffine
        (fun b => (p b).1.1.1) (fun b => (p b).1.1.2.1) (fun b => (p b).1.1.2.2) htet
        (fun b => F.cut (p b).1.1 (i₀ (p b))) (fun b => F.ball (p b).1.1 (p b).1.2)
        (fun b => (F.ball_pair (p b).1.1 (p b).1.2).isCompact.isClosed)
        (fun b => F.ball_subset_tetrahedron (p b).1.1 (p b).1.2)
        (fun b _ hx => F.component_physical hgi (p b).1.1 (p b).1.2 hx)
        (fun b => (p b).2) (fun b => H (p b)) (fun b => flip (p b))
        (fun b => hformula (p b)) ⟨hj,hl⟩ hxS
  have hsource (x : U) : g x ∉ S := by
    obtain ⟨j,hj⟩ := mem_iUnion.mp x.property
    exact hj.2
  let pieces (j : Cell) : Set U := {x | (x : E) ∈ F.ball j.1.1 j.1.2}
  let maps (j : Cell) : C(pieces j,T) :=
    ⟨fun x => ⟨prismFiberMidpoint (H j) ⟨x.1,x.2⟩,
      mem_iUnion.mpr ⟨j,prismFiberMidpoint_mem_trim (H j) ⟨x.1,x.2⟩⟩⟩,by
      exact (continuous_subtype_val.comp ((continuous_prismFiberMidpoint (H j)).comp
        ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _))).subtype_mk _⟩
  have hmaps (j l : Cell) (x : U) (hj : x ∈ pieces j) (hl : x ∈ pieces l) :
      maps j ⟨x,hj⟩ = maps l ⟨x,hl⟩ := Subtype.ext (hagree j l x hj hl (hsource x))
  have hcover : ⋃ j, pieces j = univ := by
    apply iUnion_eq_univ_iff.mpr
    intro x
    obtain ⟨j,hj⟩ := mem_iUnion.mp x.property
    exact ⟨j,hj.1⟩
  let m := Set.liftCover pieces (fun j => maps j) hmaps hcover
  have hval (j : Cell) (x : pieces j) : m x = maps j x := Set.liftCover_coe x
  have hm : Continuous m := by
    apply (locallyFinite_of_finite pieces).continuous hcover
    · intro j
      exact (F.ball_pair j.1.1 j.1.2).isCompact.isClosed.preimage continuous_subtype_val
    · intro j
      rw [continuousOn_iff_continuous_domRestrict]
      have he : (pieces j).domRestrict m = maps j := funext (hval j)
      rw [he]
      exact (maps j).continuous
  refine ⟨⟨m,hm⟩,?_⟩
  intro j x
  exact congrArg Subtype.val (hval j ⟨⟨x,mem_iUnion.mpr ⟨j,x.property⟩⟩,x.property.1⟩)

end PoincareConjecture.M76.PrismBelt
