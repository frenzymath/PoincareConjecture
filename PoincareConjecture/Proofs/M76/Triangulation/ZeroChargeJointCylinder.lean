import PoincareConjecture.Proofs.M76.Triangulation.ZeroChargeJointAnnulus
import PoincareConjecture.Proofs.M76.Mathlib.SupportedFinitePLExtension
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLArithmetic
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductBall
















set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.ZeroChargeJoint

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]







theorem exists_joint_finitePL_cylinder
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {N T : Set E} (hNK : N ⊆ K.space) (hT : IsCompact T)
    (hTN : T ⊆ interior N) {a b : ℝ} (hab : a < b)
    (H : E × ℝ → E) (hH : FinitePiecewiseAffineOn H (N ×ˢ Icc a b))
    (hsupport : ∀ p ∈ N ×ˢ Icc a b, p.1 ∉ T → H p = p.1)
    (hinj : ∀ t ∈ Icc a b, InjOn (fun x => H (x, t)) N)
    (himage : ∀ t ∈ Icc a b, (fun x => H (x, t)) '' N = N)
    (t₀ : ℝ) (hstart : ∀ x ∈ N, H (x, t₀) = x) :
    ∃ e : (K.space ×ˢ Icc a b : Set (E × ℝ)) ≃ₜ (K.space ×ˢ Icc a b),
      e.IsFinitePL ∧
      (∀ p : (K.space ×ˢ Icc a b : Set (E × ℝ)),
        (e p : E × ℝ).2 = (p : E × ℝ).2) ∧
      (∀ p : (K.space ×ˢ Icc a b : Set (E × ℝ)), (p : E × ℝ).1 ∈ N →
        (e p : E × ℝ) = (H p, (p : E × ℝ).2)) ∧
      (∀ p : (K.space ×ˢ Icc a b : Set (E × ℝ)), (p : E × ℝ).1 ∉ T → e p = p) ∧
      ∀ p : (K.space ×ˢ Icc a b : Set (E × ℝ)), (p : E × ℝ).2 = t₀ → e p = p := by
  classical
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨J, hJ, hJI, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_Icc hab
  obtain ⟨R, hR, hRprod, _⟩ := K.exists_finite_triangulation_prod J hK hJ
  have hRC : R.space = K.space ×ˢ Icc a b := by rw [hRprod, hJI]
  let fstA := (ContinuousLinearMap.fst ℝ E ℝ).toContinuousAffineMap
  let sndA := (ContinuousLinearMap.snd ℝ E ℝ).toContinuousAffineMap
  have hfstN : FinitePiecewiseAffineOn (fun p : E × ℝ => p.1) (N ×ˢ Icc a b) := by
    obtain ⟨Q, hQ, hQN, _⟩ := hH
    exact ⟨Q, hQ, hQN, Q.affineOnFaces_affine fstA⟩
  have hdisp := hH.sub hfstN
  have hsub : N ×ˢ Icc a b ⊆ R.space := by
    rw [hRC]
    exact prod_mono hNK Subset.rfl
  have hdispzero (p : E × ℝ) (hp : p ∈ N ×ˢ Icc a b)
      (houtside : p ∉ T ×ˢ Icc a b) : H p - p.1 = 0 := by
    rw [hsupport p hp (fun hx => houtside ⟨hx, hp.2⟩), sub_self]
  obtain ⟨g, hg, hgeq, hgzero, _⟩ :=
    hdisp.exists_supported_extension_of_eq_zero_off R hR hsub
      (hT.prod isCompact_Icc) hdispzero (isOpen_interior.prod isOpen_univ)
      (prod_mono hTN (subset_univ _))
  let F : E × ℝ → E × ℝ := fun p => (p.1 + g p, p.2)
  have hF : FinitePiecewiseAffineOn F (K.space ×ˢ Icc a b) := by
    rw [← hRC]
    exact (((R.affineOnFaces_affine fstA).finitePiecewiseAffineOn hR).add hg).prod_mk
      ((R.affineOnFaces_affine sndA).finitePiecewiseAffineOn hR)
  have hFinside (p : E × ℝ) (hp : p ∈ K.space ×ˢ Icc a b) (hx : p.1 ∈ N) :
      F p = (H p, p.2) := by
    change (p.1 + g p, p.2) = (H p, p.2)
    rw [hgeq ⟨hx, hp.2⟩]
    change (p.1 + (H p - p.1), p.2) = (H p, p.2)
    have hsum : p.1 + (H p - p.1) = H p := by abel
    exact congrArg (fun x : E => (x, p.2)) hsum
  have hFoutside (p : E × ℝ) (hp : p ∈ K.space ×ˢ Icc a b) (hx : p.1 ∉ T) :
      F p = p := by
    have hg0 : g p = 0 := by
      by_cases hxN : p.1 ∈ N
      · rw [hgeq ⟨hxN, hp.2⟩]
        change H p - p.1 = 0
        rw [hsupport p ⟨hxN, hp.2⟩ hx, sub_self]
      · exact hgzero p (fun hu => hxN (interior_subset hu.1))
    simp only [F, hg0, add_zero, Prod.mk.eta]
  have hnotT {x : E} (hx : x ∉ N) : x ∉ T :=
    fun h => hx (interior_subset (hTN h))
  have hFinj : InjOn F (K.space ×ˢ Icc a b) := by
    rintro ⟨x, t⟩ hp ⟨y, s⟩ hq heq
    have hts : t = s := congrArg Prod.snd heq
    subst s
    by_cases hxN : x ∈ N
    · by_cases hyN : y ∈ N
      · rw [hFinside _ hp hxN, hFinside _ hq hyN] at heq
        exact congrArg (fun x : E => (x, t)) (hinj t hp.2 hxN hyN (congrArg Prod.fst heq))
      · rw [hFinside _ hp hxN, hFoutside _ hq (hnotT hyN)] at heq
        exact (hyN ((himage t hp.2).subset ⟨x, hxN, congrArg Prod.fst heq⟩)).elim
    · by_cases hyN : y ∈ N
      · rw [hFoutside _ hp (hnotT hxN), hFinside _ hq hyN] at heq
        exact (hxN ((himage t hq.2).subset ⟨y, hyN, (congrArg Prod.fst heq).symm⟩)).elim
      · rw [hFoutside _ hp (hnotT hxN), hFoutside _ hq (hnotT hyN)] at heq
        exact heq
  have hFimage : F '' (K.space ×ˢ Icc a b) = K.space ×ˢ Icc a b := by
    apply Subset.antisymm
    · rintro p ⟨⟨x, t⟩, hp, rfl⟩
      by_cases hxN : x ∈ N
      · rw [hFinside _ hp hxN]
        exact ⟨hNK ((himage t hp.2).subset ⟨x, hxN, rfl⟩), hp.2⟩
      · rwa [hFoutside _ hp (hnotT hxN)]
    · rintro ⟨y, t⟩ hp
      by_cases hyN : y ∈ N
      · obtain ⟨x, hx, hxy⟩ := (himage t hp.2).symm.subset hyN
        change H (x, t) = y at hxy
        have hxp : (x, t) ∈ K.space ×ˢ Icc a b := ⟨hNK hx, hp.2⟩
        refine ⟨(x, t), hxp, ?_⟩
        rw [hFinside _ hxp hx, hxy]
      · exact ⟨(y, t), hp, hFoutside _ hp (hnotT hyN)⟩
  obtain ⟨e, he, heval⟩ := hF.exists_homeomorph_image hFinj
  let E' := e.trans (Homeomorph.setCongr hFimage)
  have hE : E'.IsFinitePL := he.setCongr rfl hFimage
  have hEval (p : (K.space ×ˢ Icc a b : Set (E × ℝ))) :
      (E' p : E × ℝ) = F p := heval p
  refine ⟨E', hE, ?_, ?_, ?_, ?_⟩
  · intro p
    simpa only [F] using congrArg Prod.snd (hEval p)
  · intro p hp
    exact (hEval p).trans (hFinside p p.property hp)
  · intro p hp
    exact Subtype.ext ((hEval p).trans (hFoutside p p.property hp))
  · intro p hp
    apply Subtype.ext
    rw [hEval]
    by_cases hxN : (p : E × ℝ).1 ∈ N
    · rw [hFinside p p.property hxN]
      have hHp : H (p : E × ℝ) = (p : E × ℝ).1 := by
        have hpair : (p : E × ℝ) = ((p : E × ℝ).1, t₀) := Prod.ext rfl hp
        rw [hpair]
        exact hstart _ hxN
      rw [hHp]
    · exact hFoutside p p.property (hnotT hxN)

end PoincareConjecture.M76.ZeroChargeJoint
