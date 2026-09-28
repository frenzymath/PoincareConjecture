import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Collars.PolygonLocalJordanSide
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionPLLocalInterior
import PoincareConjecture.Proofs.M76.Mathlib.PolygonSliceCoordinates
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLCoordinates

set_option autoImplicit false

open Set Geometry

namespace Polygon

theorem disjoint_transverse_strip_images {n : ℕ}
    (P : Polygon (ℝ × ℝ) (n + 3)) (hP : P.HasSimplicialEdges)
    (hinjP : Function.Injective P) {r a b : ℝ} (hr : 0 < r) (hab : a < b)
    {f : (ℝ × ℝ) → (ℝ × ℝ)}
    (hf : FinitePiecewiseAffineOn f (Icc (-r) r ×ˢ Icc a b))
    (hinj : InjOn f (Ioo (-r) r ×ˢ Ioo a b))
    (haxis : ∀ x ∈ Icc (-r) r ×ˢ Icc a b, f x ∈ P.boundary ℝ ↔ x.1 = 0) :
    Disjoint (f '' (Ioc 0 r ×ˢ Icc a b)) (f '' (Ico (-r) 0 ×ˢ Icc a b)) := by
  let S := Icc (-r) r ×ˢ Icc a b
  let A := Ioc 0 r ×ˢ Icc a b
  let B := Ico (-r) 0 ×ˢ Icc a b
  have hAS : A ⊆ S := fun x hx =>
    ⟨⟨(neg_nonpos.mpr hr.le).trans hx.1.1.le, hx.1.2⟩, hx.2⟩
  have hBS : B ⊆ S := fun x hx =>
    ⟨⟨hx.1.1, hx.1.2.le.trans hr.le⟩, hx.2⟩
  have hA : IsPreconnected (f '' A) :=
    (isPreconnected_Ioc.prod isPreconnected_Icc).image f (hf.continuousOn.mono hAS)
  have hB : IsPreconnected (f '' B) :=
    (isPreconnected_Ico.prod isPreconnected_Icc).image f (hf.continuousOn.mono hBS)
  have hcomp : f '' A ∪ f '' B ⊆ (P.boundary ℝ)ᶜ := by
    rintro y (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩) hy
    · exact hx.1.1.ne' ((haxis x (hAS hx)).mp hy)
    · exact hx.1.2.ne ((haxis x (hBS hx)).mp hy)
  let q : ℝ × ℝ := (0, (a + b) / 2)
  have hq : q ∈ Ioo (-r) r ×ˢ Ioo a b := by
    dsimp [q]
    constructor <;> constructor <;> linarith
  obtain ⟨K, hK, hconv, hqK, hKsub⟩ :=
    (isOpen_Ioo.prod isOpen_Ioo).exists_finite_convex_neighborhood hq
  have hKS : K.space ⊆ S := fun x hx =>
    ⟨⟨(hKsub hx).1.1.le, (hKsub hx).1.2.le⟩,
      (hKsub hx).2.1.le, (hKsub hx).2.2.le⟩
  have hqU : f q ∈ interior (f '' K.space) :=
    (hf.restrict K hK hKS).mem_interior_image_of_convex hconv rfl
      (hinj.mono hKsub) hqK
  have hqP : f q ∈ P.boundary ℝ :=
    (haxis q (hKS (interior_subset hqK))).mpr rfl
  have hcover : interior (f '' K.space) \ P.boundary ℝ ⊆ f '' A ∪ f '' B := by
    rintro y ⟨hy, hyP⟩
    obtain ⟨x, hxK, rfl⟩ := interior_subset hy
    have hx := hKS hxK
    have hx0 : x.1 ≠ 0 := fun heq => hyP ((haxis x hx).mpr heq)
    rcases lt_or_gt_of_ne hx0 with hn | hp
    · exact Or.inr ⟨x, ⟨⟨hx.1.1, hn⟩, hx.2⟩, rfl⟩
    · exact Or.inl ⟨x, ⟨⟨hp, hx.1.2⟩, hx.2⟩, rfl⟩
  apply Set.disjoint_left.mpr
  intro y hyA hyB
  have hconnected : IsPreconnected (f '' A ∪ f '' B) := hA.union y hyA hyB hB
  have hsides := hconnected.subset_or_subset (P.isOpen_inside hP hinjP)
    (P.isOpen_outside hP hinjP) P.disjoint_inside_outside
    (hcomp.trans P.compl_boundary_eq_inside_union_outside.subset)
  rcases hsides with hinside | houtside
  · have hqcl : f q ∈ closure P.outside :=
      frontier_subset_closure ((P.frontier_outside hP hinjP).symm ▸ hqP)
    obtain ⟨z, hzU, hzO⟩ := mem_closure_iff.mp hqcl _ isOpen_interior hqU
    exact Set.disjoint_left.mp P.disjoint_inside_outside
      (hinside (hcover ⟨hzU, hzO.1⟩)) hzO
  · have hqcl : f q ∈ closure P.inside :=
      frontier_subset_closure ((P.frontier_inside hP hinjP).symm ▸ hqP)
    obtain ⟨z, hzU, hzI⟩ := mem_closure_iff.mp hqcl _ isOpen_interior hqU
    exact Set.disjoint_left.mp P.disjoint_inside_outside hzI
      (houtside (hcover ⟨hzU, hzI.1⟩))

theorem strip_closing_sign_eq_true {n : ℕ}
    (P : Polygon (ℝ × ℝ) (n + 3)) (hP : P.HasSimplicialEdges)
    (hinjP : Function.Injective P) {r a b : ℝ} (hr : 0 < r) (hab : a < b)
    {f : (ℝ × ℝ) → (ℝ × ℝ)}
    (hf : FinitePiecewiseAffineOn f (Icc (-r) r ×ˢ Icc a b))
    (hinj : InjOn f (Ioo (-r) r ×ˢ Ioo a b))
    (haxis : ∀ x ∈ Icc (-r) r ×ˢ Icc a b, f x ∈ P.boundary ℝ ↔ x.1 = 0)
    (sign : Bool) (hclose : f (r, a) = f ((if sign then r else -r), b)) :
    sign = true := by
  cases sign with
  | true => rfl
  | false =>
    have hd := P.disjoint_transverse_strip_images hP hinjP hr hab hf hinj haxis
    apply False.elim
    apply Set.disjoint_left.mp hd (mem_image_of_mem f (show (r, a) ∈
      Ioc 0 r ×ˢ Icc a b from ⟨⟨hr, le_rfl⟩, le_rfl, hab.le⟩))
    rw [hclose]
    exact mem_image_of_mem f (show (-r, b) ∈ Ico (-r) 0 ×ˢ Icc a b from
      ⟨⟨le_rfl, neg_lt_zero.mpr hr⟩, hab.le, le_rfl⟩)

theorem strip_closing_sign_eq_true_in_coordinates
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : E ≃L[ℝ] (ℝ × ℝ)) {n : ℕ}
    (P : Polygon E (n + 3)) (hP : P.HasSimplicialEdges)
    (hinjP : Function.Injective P) {r a b : ℝ} (hr : 0 < r) (hab : a < b)
    {f : (ℝ × ℝ) → E}
    (hf : FinitePiecewiseAffineOn f (Icc (-r) r ×ˢ Icc a b))
    (hinj : InjOn f (Ioo (-r) r ×ˢ Ioo a b))
    (haxis : ∀ x ∈ Icc (-r) r ×ˢ Icc a b, f x ∈ P.boundary ℝ ↔ x.1 = 0)
    (sign : Bool) (hclose : f (r, a) = f ((if sign then r else -r), b)) :
    sign = true := by
  let Q := P.affineImage e.toLinearEquiv.toAffineEquiv.toAffineMap
  have hQ := P.affineImage_of_leftInvOn hP hinjP
    e.toLinearEquiv.toAffineEquiv.toAffineMap
    e.symm.toLinearEquiv.toAffineEquiv.toAffineMap (fun _ _ => e.symm_apply_apply _)
  apply Q.strip_closing_sign_eq_true hQ.2.1 hQ.1 hr hab
    (hf.postcomp e.toContinuousLinearMap.toContinuousAffineMap)
    (fun _ hx _ hy hxy => hinj hx hy (e.injective hxy)) ?_ sign (congrArg e hclose)
  intro x hx
  change e (f x) ∈ (P.affineImage _).boundary ℝ ↔ x.1 = 0
  rw [P.affineImage_boundary]
  exact (e.injective.mem_set_image).trans (haxis x hx)

end Polygon
