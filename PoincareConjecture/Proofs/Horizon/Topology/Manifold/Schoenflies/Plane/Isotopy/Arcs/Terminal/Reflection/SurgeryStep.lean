import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Step
import PoincareConjecture.Proofs.Horizon.Geometry.Euclidean.PlaneLift.Reflection
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Arc.Separation.Orientation.AnnularReflection

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.SphereSurgeryStep

open Poincare.Geometry.Euclidean Poincare.Geometry.Manifold
open Saddle.Wall.Arc.Separation.Orientation

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1

theorem sphere_embedding_postcompose
    (J : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    {f : S2 → E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f) :
    _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (J ∘ f) := by
  apply isSmoothEmbedding_of_injective_mfderiv (J.contMDiff.comp hf.contMDiff)
    (J.injective.comp hf.isEmbedding.injective)
  intro q
  rw [mfderiv_comp q (J.contMDiff.mdifferentiable (by simp) _)
    (hf.contMDiff.mdifferentiable (by simp) _)]
  exact (J.mfderivToContinuousLinearEquiv (by simp) (f q)).injective.comp
    ((hf.isImmersion.isImmersionAt q).injective_mfderiv_modelWithCornersSelf (by simp))

private theorem injective_derivative_postcompose
    (J : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    {k : E2 → E3} (hk : ContDiff Real ∞ k)
    (hki : ∀ x, Injective (fderiv Real k x)) (x : E2) :
    Injective (fderiv Real (J ∘ k) x) := by
  rw [fderiv_comp x (J.contMDiff.contDiff.differentiable (by simp) _)
    (hk.differentiable (by simp) _)]
  apply Injective.comp ?_ (hki x)
  have hi := (J.mfderivToContinuousLinearEquiv (by simp) (k x)).injective
  change Injective (mfderiv (𝓡 3) (𝓡 3) J (k x)) at hi
  rw [mfderiv_eq_fderiv] at hi
  convert! hi using 1

variable {f : S2 → E3} {v : E3} {c R : Real}

def reflected (S : SphereSurgeryStep f v c R) :
    SphereSurgeryStep (heightReflection S.unit_v ∘ f) v (-c) R := by
  let J := heightReflection S.unit_v
  let D := J.trans (S.D.trans J)
  let T := reflectedAnnularChart S.T
  have hD (q : S2) : D ((J ∘ f) q) = J (S.D (f q)) := by
    change J (S.D (J (J (f q)))) = _
    rw [heightReflection_heightReflection]
  have hDfun : (fun q : S2 => D ((J ∘ f) q)) = J ∘ (fun q => S.D (f q)) := funext hD
  have hslab : T '' (univ ×ˢ Icc (-S.a) S.a) =
      S.T '' (univ ×ˢ Icc (-S.a) S.a) := by
    ext q
    constructor
    · rintro ⟨⟨u, t⟩, ⟨hu, ht⟩, heq⟩
      exact ⟨(u, -t), ⟨hu, by constructor <;> linarith [ht.1, ht.2]⟩, heq⟩
    · rintro ⟨⟨u, t⟩, ⟨hu, ht⟩, heq⟩
      refine ⟨(u, -t), ⟨hu, by constructor <;> linarith [ht.1, ht.2]⟩, ?_⟩
      simpa only [T, reflectedAnnularChart_apply, neg_neg] using heq
  have hparallel (t : Real) (ht : t ∈ Icc (-(2 * S.a)) (2 * S.a)) :
      ((fun x : Hemisphere.Plane v => (-c + t) • v + (S.A x : E3)) '' closedBall 0 1) ∩
        range (fun q => D ((J ∘ f) q)) =
      (fun q => D ((J ∘ f) q)) '' range (fun q : S1 => T (q, t)) := by
    have hneg : -t ∈ Icc (-(2 * S.a)) (2 * S.a) := by
      constructor <;> linarith [ht.1, ht.2]
    have hplane : J '' ((fun x : Hemisphere.Plane v =>
        (c + -t) • v + (S.A x : E3)) '' closedBall 0 1) =
        (fun x : Hemisphere.Plane v => (-c + t) • v + (S.A x : E3)) '' closedBall 0 1 := by
      rw [image_image]
      apply image_congr
      intro x _
      change J ((c + -t) • v + (S.A x : E3)) = _
      rw [heightReflection_height_add_plane]
      congr 2
      ring
    rw [hDfun, ← hplane, range_comp, ← image_inter (f := (J : E3 → E3)) J.injective,
      S.parallel_disk_intersection (-t) hneg, image_image]
    rfl
  refine {
    original_embedding := sphere_embedding_postcompose J S.original_embedding
    unit_v := S.unit_v
    p := S.p
    center_height := by
      simpa only [comp_apply, J, inner_heightReflection] using (congrArg Neg.neg S.center_height)
    D := D
    height_preserving := ?_
    fixed_plane := ?_
    K := J '' S.K
    compact_K := S.compact_K.image J.continuous
    support_subset := ?_
    eq_self_off := ?_
    prepared_embedding := hDfun.symm ▸ sphere_embedding_postcompose J S.prepared_embedding
    ε := S.ε
    ε_pos := S.ε_pos
    ε_lt_R := S.ε_lt_R
    T := T
    tube_source := by
      simpa only [T, neg_neg] using (reflectedAnnularChart_source S.T S.tube_source)
    tube_smooth := reflectedAnnularChart_smooth S.T S.tube_smooth
    tube_symm_smooth := reflectedAnnularChart_symm_smooth S.T S.tube_symm_smooth
    center_range := ?_
    γ := S.γ
    circle_embedding := S.circle_embedding
    cylinder := ?_
    A := S.A
    circle_image := S.circle_image
    disk_intersection := by
      simpa only [add_zero] using (hparallel 0 ⟨by linarith [S.a_pos], by linarith [S.a_pos]⟩)
    a := S.a
    a_pos := S.a_pos
    a_lt_quarter_ε := S.a_lt_quarter_ε
    a_lt_quarter_R := S.a_lt_quarter_R
    s := S.s
    s_pos := S.s_pos
    s_lt_eighth_a := S.s_lt_eighth_a
    eMinus := S.ePlus
    ePlus := S.eMinus
    eMinus_source := S.ePlus_source
    ePlus_source := S.eMinus_source
    eMinus_smooth := S.ePlus_smooth
    eMinus_symm_smooth := S.ePlus_symm_smooth
    ePlus_smooth := S.eMinus_smooth
    ePlus_symm_smooth := S.eMinus_symm_smooth
    retained_disjoint := S.retained_disjoint.symm
    eMinus_boundary := by simpa only [T, reflectedAnnularChart_apply, neg_neg] using S.ePlus_boundary
    ePlus_boundary := S.eMinus_boundary
    disk_slab_cover := by
      rw [hslab]
      convert S.disk_slab_cover using 1
      ext x
      simp only [mem_union]
      tauto
    slab_eq := by rw [hslab, S.slab_eq, union_comm]
    dMinus := S.dPlus
    dPlus := S.dMinus
    dMinus_source := S.dPlus_source
    dPlus_source := S.dMinus_source
    dMinus_smooth := S.dPlus_smooth
    dMinus_symm_smooth := S.dPlus_symm_smooth
    dPlus_smooth := S.dMinus_smooth
    dPlus_symm_smooth := S.dMinus_symm_smooth
    dMinus_closed := S.dPlus_closed
    dMinus_open := S.dPlus_open
    dPlus_closed := S.dMinus_closed
    dPlus_open := S.dMinus_open
    gMinus := J ∘ S.gPlus
    gPlus := J ∘ S.gMinus
    gMinus_smooth := J.contMDiff.contDiff.comp S.gPlus_smooth
    gPlus_smooth := J.contMDiff.contDiff.comp S.gMinus_smooth
    gMinus_injective := J.injective.comp S.gPlus_injective
    gPlus_injective := J.injective.comp S.gMinus_injective
    gMinus_deriv_injective := injective_derivative_postcompose J S.gPlus_smooth S.gPlus_deriv_injective
    gPlus_deriv_injective := injective_derivative_postcompose J S.gMinus_smooth S.gMinus_deriv_injective
    gMinus_width := ?_
    gPlus_width := ?_
    gMinus_range := ?_
    gPlus_range := ?_
    fMinus := J ∘ S.fPlus
    fPlus := J ∘ S.fMinus
    fMinus_embedding := sphere_embedding_postcompose J S.fPlus_embedding
    fPlus_embedding := sphere_embedding_postcompose J S.fMinus_embedding
    children_disjoint := ?_
    capMinus_eq := fun x hx => congrArg J (S.capPlus_eq x hx)
    capPlus_eq := fun x hx => congrArg J (S.capMinus_eq x hx)
    retainedMinus_eq := fun y hy => (congrArg J (S.retainedPlus_eq y hy)).trans (hD y).symm
    retainedPlus_eq := fun y hy => (congrArg J (S.retainedMinus_eq y hy)).trans (hD y).symm
    fMinus_range := ?_
    fPlus_range := ?_
    parallel_disk_intersection := hparallel }
  · intro x
    change inner Real v (J (S.D (J x))) = _
    simp only [J, inner_heightReflection, S.height_preserving, neg_neg]
  · intro x hx
    change J (S.D (J x)) = x
    have hJx : inner Real v (J x) = c := by rw [inner_heightReflection, hx, neg_neg]
    rw [S.fixed_plane _ hJx, heightReflection_heightReflection]
  · rintro y ⟨x, hx, rfl⟩
    have h : |inner Real v x - c| ≤ R := S.support_subset hx
    change |inner Real v (J x) - -c| ≤ R
    simpa only [J, inner_heightReflection, neg_sub_neg, abs_sub_comm] using h
  · intro x hx
    change J (S.D (J x)) = x
    have hJx : J x ∉ S.K := by
      intro hmem
      exact hx ⟨J x, hmem, heightReflection_heightReflection S.unit_v x⟩
    rw [S.eq_self_off _ hJx, heightReflection_heightReflection]
  · simpa only [T, reflectedAnnularChart_apply, neg_zero, comp_apply, J,
      inner_heightReflection, preimage, mem_singleton_iff, neg_inj] using S.center_range
  · intro q t ht
    rw [hD]
    change J (S.D (f (S.T (q, -t)))) = _
    rw [S.cylinder q (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩,
      heightReflection_height_add_plane]
    congr 2
    ring
  · intro x
    change |inner Real v (J (S.gPlus x)) - (-c - S.a)| < S.a / 2
    rw [inner_heightReflection, show -inner Real v (S.gPlus x) - (-c - S.a) =
      -(inner Real v (S.gPlus x) - (c + S.a)) by ring, abs_neg]
    exact S.gPlus_width x
  · intro x
    change |inner Real v (J (S.gMinus x)) - (-c + S.a)| < S.a / 2
    rw [inner_heightReflection, show -inner Real v (S.gMinus x) - (-c + S.a) =
      -(inner Real v (S.gMinus x) - (c - S.a)) by ring, abs_neg]
    exact S.gMinus_width x
  · rw [image_comp, S.gPlus_range, image_heightReflection_liftPlaneDiffeomorph]
    simp only [neg_add_rev, neg_neg]
    congr 2 <;> ring
  · rw [image_comp, S.gMinus_range, image_heightReflection_liftPlaneDiffeomorph]
    congr 2 <;> ring
  · apply disjoint_left.mpr
    rintro x ⟨q, rfl⟩ ⟨r, hr⟩
    exact disjoint_left.mp S.children_disjoint (mem_range_self r)
      ⟨q, (J.injective hr).symm⟩
  · rw [range_comp, S.fPlus_range, image_union, image_image, hDfun]
    rw [image_image]
    rfl
  · rw [range_comp, S.fMinus_range, image_union, image_image, hDfun]
    rw [image_image]
    rfl

@[simp] theorem reflected_fMinus (S : SphereSurgeryStep f v c R) :
    S.reflected.fMinus = heightReflection S.unit_v ∘ S.fPlus := rfl

@[simp] theorem reflected_fPlus (S : SphereSurgeryStep f v c R) :
    S.reflected.fPlus = heightReflection S.unit_v ∘ S.fMinus := rfl

@[simp] theorem reflected_eMinus (S : SphereSurgeryStep f v c R) : S.reflected.eMinus = S.ePlus := rfl
@[simp] theorem reflected_ePlus (S : SphereSurgeryStep f v c R) : S.reflected.ePlus = S.eMinus := rfl
@[simp] theorem reflected_dMinus (S : SphereSurgeryStep f v c R) : S.reflected.dMinus = S.dPlus := rfl
@[simp] theorem reflected_dPlus (S : SphereSurgeryStep f v c R) : S.reflected.dPlus = S.dMinus := rfl
@[simp] theorem reflected_a (S : SphereSurgeryStep f v c R) : S.reflected.a = S.a := rfl
@[simp] theorem reflected_s (S : SphereSurgeryStep f v c R) : S.reflected.s = S.s := rfl

end Poincare.Manifold.Schoenflies.SphereSurgeryStep
