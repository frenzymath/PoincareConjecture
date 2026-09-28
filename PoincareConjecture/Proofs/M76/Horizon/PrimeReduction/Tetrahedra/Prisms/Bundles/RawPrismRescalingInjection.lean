import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.OriginalRegularPrismAffineFiber
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.OriginalVariableTrimmedReflection
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.EndpointOrbitCover



set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1
local notation "Square" => (I ×ˢ I : Set (ℝ × ℝ))

theorem prism_mem_ends_iff
    {E : Type*} [TopologicalSpace E] {A B : Set E}
    (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B) (y : A ×ˢ I) :
    (H y : E) ∈ prismEnds H ↔ (y : E × ℝ).2 = 0 ∨ (y : E × ℝ).2 = 1 := by
  constructor
  · rintro ⟨⟨a,b⟩,h⟩
    have he := H.injective (Subtype.ext h)
    have ht := congrArg (fun z : A ×ˢ I => (z : E × ℝ).2) he
    cases b <;> simp only [Bool.false_eq_true, if_false, if_true] at ht
    · exact Or.inl ht.symm
    · exact Or.inr ht.symm
  · rintro (h | h)
    · refine ⟨(⟨(y : E × ℝ).1,y.property.1⟩,false),?_⟩
      apply congrArg (fun z => (H z : E))
      exact Subtype.ext (Prod.ext rfl h.symm)
    · refine ⟨(⟨(y : E × ℝ).1,y.property.1⟩,true),?_⟩
      apply congrArg (fun z => (H z : E))
      exact Subtype.ext (Prod.ext rfl h.symm)

theorem raw_prism_rescaling_mem_caps_iff
    {E ι : Type*} [TopologicalSpace E] (A B T : ι → Set E) (S : Set E)
    (H : ∀j, (A j ×ˢ I : Set (E × ℝ)) ≃ₜ B j)
    (C : ∀j, (A j ×ˢ I : Set (E × ℝ)) ≃ₜ T j)
    (hcap : ∀j y, (H j y : E) ∈ S ↔ (y : E × ℝ).2 = 0 ∨ (y : E × ℝ).2 = 1)
    (r : E → E) (hr : ∀j y, r (C j y) = H j y)
    {x : E} (hx : x ∈ ⋃j,T j) :
    r x ∈ S ↔ x ∈ ⋃j,prismEnds (C j) := by
  constructor
  · intro hs
    obtain ⟨j,hj⟩ := mem_iUnion.mp hx
    let y := (C j).symm ⟨x,hj⟩
    have hv : (C j y : E) = x := congrArg Subtype.val ((C j).apply_symm_apply _)
    have ht : (y : E × ℝ).2 = 0 ∨ (y : E × ℝ).2 = 1 :=
      (hcap j y).mp (by rw [← hr, hv]; exact hs)
    exact mem_iUnion.mpr ⟨j,hv ▸ (prism_mem_ends_iff (C j) y).mpr ht⟩
  · intro he
    obtain ⟨j,⟨⟨a,b⟩,rfl⟩⟩ := mem_iUnion.mp he
    unfold prismEndMap
    rw [hr,hcap]
    cases b <;> simp

theorem quarter_recovery_admissible
    {E : Type*} [TopologicalSpace E] {A B : Set E}
    (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B) (y : B) :
    affineFiberHeight (1/4) (H.symm y : E × ℝ).2 ∈ I := by
  have ht := (H.symm y).property.2
  unfold affineFiberHeight
  constructor <;> linarith [ht.1,ht.2]

theorem quarter_prism_recovery
    {E : Type*} [TopologicalSpace E] {A B : Set E}
    (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B)
    (C : (A ×ˢ I : Set (E × ℝ)) ≃ₜ prismTrim H)
    (hCv : ∀ x, (C x : E) = H (trimProduct A x)) (y : B) :
    (C (H.symm y) : E) =
      prismAffineFiberPoint H y (1/4) (quarter_recovery_admissible H y) := by
  rw [hCv]
  change (H _ : E) = H _
  congr 2
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change 1/4+(H.symm y : E × ℝ).2/2 =
      (1-1/4)*(H.symm y : E × ℝ).2+(1/4)*(1-(H.symm y : E × ℝ).2)
    ring

set_option maxHeartbeats 600000 in
theorem original_raw_prism_rescaling_injOn
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
    (r : E → E) (hr : ∀ j x, r (C j x) = H j x) :
    InjOn r ((⋃ j, prismTrim (H j)) \ r ⁻¹' (g ⁻¹' S)) := by
  intro x hx y hy hxy
  obtain ⟨j,hj⟩ := mem_iUnion.mp hx.1
  obtain ⟨l,hl⟩ := mem_iUnion.mp hy.1
  let sx := (C j).symm ⟨x,hj⟩
  let sy := (C l).symm ⟨y,hl⟩
  have hrx : r x = H j sx := by simpa only [sx,(C j).apply_symm_apply] using hr j sx
  have hry : r y = H l sy := by simpa only [sy,(C l).apply_symm_apply] using hr l sy
  have hzj : r x ∈ F.ball j.1.1 j.1.2 := hrx ▸ (H j sx).property
  have hzl : r x ∈ F.ball l.1.1 l.1.2 := (hxy.trans hry) ▸ (H l sy).property
  have hbackj : (C j ((H j).symm ⟨r x,hzj⟩) : E) = x := by
    have he : (⟨r x,hzj⟩ : F.ball j.1.1 j.1.2) = H j sx := Subtype.ext hrx
    rw [he,(H j).symm_apply_apply]
    exact congrArg Subtype.val ((C j).apply_symm_apply ⟨x,hj⟩)
  have hbackl : (C l ((H l).symm ⟨r x,hzl⟩) : E) = y := by
    have he : (⟨r x,hzl⟩ : F.ball l.1.1 l.1.2) = H l sy := Subtype.ext (hxy.trans hry)
    rw [he,(H l).symm_apply_apply]
    exact congrArg Subtype.val ((C l).apply_symm_apply ⟨y,hl⟩)
  have hh := original_regular_prism_affine_fiber_agrees K g hgi D G hW hZ hL haffine
    F i₀ H flip hformula j l (r x) hzj hzl hx.2 (1/4)
    (quarter_recovery_admissible (H j) ⟨r x,hzj⟩)
    (quarter_recovery_admissible (H l) ⟨r x,hzl⟩)
  exact hbackj.symm.trans ((quarter_prism_recovery (H j) (C j) (hCv j) _).trans
    (hh.trans ((quarter_prism_recovery (H l) (C l) (hCv l) _).symm.trans hbackl)))

end PoincareConjecture.M76.PrismBelt
