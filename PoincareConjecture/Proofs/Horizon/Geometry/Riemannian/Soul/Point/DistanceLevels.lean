import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Point.Basic

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.RiemannianMetric.RadialHomeomorph

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {p : M}

theorem radius_symm (H : RadialHomeomorph g p) (x : {x : M // x ≠ p}) :
    ((H.toHomeomorph.symm x).2 : ℝ) = (g.edist p x).toReal := by
  simpa only [Homeomorph.apply_symm_apply] using
    (H.distance_eq (H.toHomeomorph.symm x)).symm

private theorem ne_center_of_positive_distance {x : M}
    (hx : 0 < (g.edist p x).toReal) : x ≠ p := by
  intro hxp
  subst x
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  simp only [RiemannianMetric.edist, Manifold.riemannianEDist_self,
    ENNReal.toReal_zero, lt_self_iff_false] at hx

def distanceRestriction (H : RadialHomeomorph g p) (I : Set ℝ)
    (hI : ∀ r ∈ I, 0 < r) :
    (UnitTwoSphere × I) ≃ₜ {x : M // (g.edist p x).toReal ∈ I} where
  toFun z := ⟨H.toHomeomorph (z.1, ⟨z.2, hI z.2 z.2.property⟩), by
    rw [H.distance_eq]
    exact z.2.property⟩
  invFun x :=
    let y : {x : M // x ≠ p} :=
      ⟨x, ne_center_of_positive_distance (hI _ x.property)⟩
    ((H.toHomeomorph.symm y).1, ⟨(H.toHomeomorph.symm y).2, by
      rw [H.radius_symm y]
      exact x.property⟩)
  left_inv z := by
    have hx : (⟨(H.toHomeomorph (z.1, ⟨z.2, hI z.2 z.2.property⟩) : M),
        ne_center_of_positive_distance (hI _ (by
          rw [H.distance_eq]
          exact z.2.property))⟩ : {x : M // x ≠ p}) =
        H.toHomeomorph (z.1, ⟨z.2, hI z.2 z.2.property⟩) := rfl
    simp only [hx, Homeomorph.symm_apply_apply]
  right_inv x := by
    apply Subtype.ext
    exact congrArg (fun y : {x : M // x ≠ p} => (y : M)) (H.toHomeomorph.apply_symm_apply
      ⟨x, ne_center_of_positive_distance (hI _ x.property)⟩)
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp (H.toHomeomorph.continuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd |>.subtype_mk _)))
  continuous_invFun := by
    have hy : Continuous (fun x : {x : M // (g.edist p x).toReal ∈ I} =>
        (⟨x, ne_center_of_positive_distance (hI _ x.property)⟩ : {x : M // x ≠ p})) :=
      continuous_subtype_val.subtype_mk _
    exact (continuous_fst.comp (H.toHomeomorph.symm.continuous.comp hy)).prodMk
      ((continuous_subtype_val.comp
        (continuous_snd.comp (H.toHomeomorph.symm.continuous.comp hy))).subtype_mk _)

@[simp] theorem distanceRestriction_apply (H : RadialHomeomorph g p) (I : Set ℝ)
    (hI : ∀ r ∈ I, 0 < r) (z : UnitTwoSphere × I) :
    ((H.distanceRestriction I hI z : {x : M // (g.edist p x).toReal ∈ I}) : M) =
      H.toHomeomorph (z.1, ⟨z.2, hI z.2 z.2.property⟩) := rfl

def sphere (H : RadialHomeomorph g p) (r : ℝ) (hr : 0 < r) :
    UnitTwoSphere ≃ₜ distanceSphere g p r :=
  (Homeomorph.prodUnique UnitTwoSphere {s : ℝ // s = r}).symm.trans
    (H.distanceRestriction {s | s = r} (fun _ hs => hs ▸ hr))

@[simp] theorem sphere_apply (H : RadialHomeomorph g p) (r : ℝ) (hr : 0 < r)
    (θ : UnitTwoSphere) :
    ((H.sphere r hr θ : distanceSphere g p r) : M) =
      H.toHomeomorph (θ, ⟨r, hr⟩) := rfl

def annulus (H : RadialHomeomorph g p) (a b : ℝ) (ha : 0 < a) :
    (UnitTwoSphere × Icc a b) ≃ₜ distanceAnnulus g p a b :=
  H.distanceRestriction (Icc a b) (fun _ hr => ha.trans_le hr.1)

@[simp] theorem annulus_apply (H : RadialHomeomorph g p) (a b : ℝ) (ha : 0 < a)
    (z : UnitTwoSphere × Icc a b) :
    ((H.annulus a b ha z : distanceAnnulus g p a b) : M) =
      H.toHomeomorph (z.1, ⟨z.2, ha.trans_le z.2.property.1⟩) := rfl

theorem annulus_eq_sphere (H : RadialHomeomorph g p) (a b r : ℝ)
    (ha : 0 < a) (hr : r ∈ Icc a b) (θ : UnitTwoSphere) :
    ((H.annulus a b ha (θ, ⟨r, hr⟩) : distanceAnnulus g p a b) : M) =
      ((H.sphere r (ha.trans_le hr.1) θ : distanceSphere g p r) : M) := rfl

end PoincareConjecture.RiemannianMetric.RadialHomeomorph
