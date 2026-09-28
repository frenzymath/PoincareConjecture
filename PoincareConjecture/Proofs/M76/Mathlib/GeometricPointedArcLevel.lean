import PoincareConjecture.Proofs.M76.Mathlib.PointedCapArcReplacement

set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem IsFinitePL.exists_pointed_cap_collar_level_arc
    {B T d b : Set E} {upper g r : E → ℝ}
    {C : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)} ≃ₜ T}
    (A : E →ᵃ[ℝ] ℝ) (hheight : ∀ p, A (C p) = (p : E × ℝ).2)
    (hbottom : ∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
      (p : E × ℝ).2 = 0 → (C p : E) = (p : E × ℝ).1)
    (hdplane : d ⊆ {x | A x = 0}) (hcap : d ∩ T = b)
    (H : E ≃ₜ E) {t a : ℝ} (ht : 0 < t)
    (hgr : EqOn g r d) (hHheight : ∀ x ∈ d, A (H x) = t * r x)
    (hhigh : ∀ x ∈ b, a ≤ r x → t * a < upper x)
    (hrlo : IsFinitePLBallPair ℝ (b ∩ {x | r x ≤ a}) (b ∩ {x | r x = a}))
    (hrhi : IsFinitePLBallPair ℝ (b ∩ {x | a ≤ r x}) (b ∩ {x | r x = a}))
    (hwidth : IsFinitePLBallPair ℝ (b ∩ {x | t * a ≤ upper x})
      (b ∩ {x | upper x = t * a}))
    (hcaplevel : IsFinitePLBallPair ℝ ((H '' d) ∩ {x | A x = t * a})
      ((H '' b) ∩ {x | A x = t * a}))
    {L : {x : E | x ∈ B ∧ t * a ∈ Icc (t * g x) (upper x)} ≃ₜ
      ((H '' T) ∩ {x | A x = t * a} : Set E)} (hL : L.IsFinitePL)
    (hLp : ∀ x : {x : E | x ∈ B ∧ t * a ∈ Icc (t * g x) (upper x)},
      ∃ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
        (p : E × ℝ).1 = (x : E) ∧ (L x : E) = H (C p) ∧
        (t * g x = t * a ↔ (p : E × ℝ).2 = 0) ∧
        (upper x = t * a ↔ (p : E × ℝ).2 = upper x)) :
    ∃ f : E → E, (∀ x, (L x : E) = f x) ∧
      FinitePiecewiseAffineOn f ((b ∩ {x | r x ≤ a}) ∩ {x | t * a ≤ upper x}) ∧
      IsFinitePLBallPair ℝ
        (((H '' d) ∩ {x | A x = t * a}) ∪
          f '' ((b ∩ {x | r x ≤ a}) ∩ {x | t * a ≤ upper x}))
        (f '' (b ∩ {x | upper x = t * a})) ∧
      ∀ x ∈ b ∩ {x | r x = a}, f x = H x := by
  obtain ⟨f, hf, hfval⟩ := hL
  have hbd : b ⊆ d := hcap.symm.subset.trans inter_subset_left
  have hbT : b ⊆ T := hcap.symm.subset.trans inter_subset_right
  have hbB : b ⊆ B := by
    intro x hx
    let p := C.symm ⟨x, hbT hx⟩
    have hCp : (C p : E) = x := congrArg Subtype.val (C.apply_symm_apply _)
    have hp0 : (p : E × ℝ).2 = 0 :=
      (hheight p).symm.trans ((congrArg A hCp).trans (hdplane (hbd hx)))
    have hpx : (p : E × ℝ).1 = x := (hbottom p hp0).symm.trans hCp
    exact hpx ▸ p.property.1
  let J : Set E := (b ∩ {x | r x ≤ a}) ∩ {x | t * a ≤ upper x}
  have hJS : J ⊆ {x : E | x ∈ B ∧ t * a ∈ Icc (t * g x) (upper x)} := by
    intro x hx
    refine ⟨hbB hx.1.1, ?_, hx.2⟩
    rw [hgr (hbd hx.1.1)]
    exact mul_le_mul_of_nonneg_left hx.1.2 ht.le
  obtain ⟨_, hinter, houter⟩ := rim_superlevel_truncated_sublevel_partition hhigh
  have hqJ : b ∩ {x | r x = a} ⊆ J := hinter.symm.subset.trans inter_subset_right
  have htriLo := hrlo
  have htriHi := hwidth
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := htriLo
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨N, hN, hNs, _⟩, _⟩, _⟩ := htriHi
  obtain ⟨P, hP, hPs⟩ := K.exists_finite_triangulation_inter N hK hN
  have hPJ : P.space = J := by
    rw [hPs, hKs, hNs]
    ext x
    change ((x ∈ b ∧ r x ≤ a) ∧ x ∈ b ∧ t * a ≤ upper x) ↔
      (x ∈ b ∧ r x ≤ a) ∧ t * a ≤ upper x
    tauto
  have hfJ : FinitePiecewiseAffineOn f J := by
    rw [← hPJ]
    exact hf.restrict P hP (hPJ.subset.trans hJS)
  have hinj : InjOn f J := by
    intro x hx y hy hxy
    have heq : L ⟨x, hJS hx⟩ = L ⟨y, hJS hy⟩ := by
      apply Subtype.ext
      simpa only [hfval] using hxy
    exact congrArg Subtype.val (L.injective heq)
  have hlow (x : E) (hx : x ∈ b ∩ {x | r x = a}) : f x = H x := by
    obtain ⟨p, hpbase, hpval, hplo, _⟩ := hLp ⟨x, hJS (hqJ hx)⟩
    have hzero : (p : E × ℝ).2 = 0 := hplo.mp (by rw [hgr (hbd hx.1), hx.2])
    have hCp : (C p : E) = x := (hbottom p hzero).trans hpbase
    exact (hfval _).symm.trans (hpval.trans (congrArg H hCp))
  have hinc (x : E) (hx : x ∈ J) : f x ∈ H '' d ↔ r x = a := by
    constructor
    · rintro ⟨y, hy, hyf⟩
      obtain ⟨p, _, hpval, hplo, _⟩ := hLp ⟨x, hJS hx⟩
      have hCp : (C p : E) = y :=
        H.injective (hpval.symm.trans ((hfval _).trans hyf.symm))
      have hp0 : (p : E × ℝ).2 = 0 :=
        (hheight p).symm.trans ((congrArg A hCp).trans (hdplane hy))
      have hmul := hplo.mpr hp0
      rw [hgr (hbd hx.1.1)] at hmul
      exact mul_left_cancel₀ ht.ne' hmul
    · intro hxa
      rw [hlow x ⟨hx.1.1, hxa⟩]
      exact mem_image_of_mem H (hbd hx.1.1)
  have hboundary : f '' (b ∩ {x | r x = a}) = (H '' b) ∩ {x | A x = t * a} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hlow x hx]
      exact ⟨mem_image_of_mem H hx.1, (hHheight x (hbd hx.1)).trans
        (congrArg (t * ·) hx.2)⟩
    · rintro ⟨⟨x, hx, rfl⟩, hxa⟩
      have hlevel : r x = a :=
        mul_left_cancel₀ ht.ne' ((hHheight x (hbd hx)).symm.trans hxa)
      exact ⟨x, ⟨hx, hlevel⟩, hlow x ⟨hx, hlevel⟩⟩
  have hcapPL : IsFinitePLBallPair ℝ ((H '' d) ∩ {x | A x = t * a})
      (f '' (b ∩ {x | r x = a})) := hboundary.symm ▸ hcaplevel
  have hInter : ((H '' d) ∩ {x | A x = t * a}) ∩ f '' J =
      f '' (b ∩ {x | r x = a}) := by
    ext y
    constructor
    · rintro ⟨hy, x, hx, rfl⟩
      exact ⟨x, ⟨hx.1.1, (hinc x hx).mp hy.1⟩, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hcapPL.1 (mem_image_of_mem f hx), mem_image_of_mem f (hqJ hx)⟩
  exact ⟨f, hfval, hfJ,
    hwidth.pointed_arc_replacement hrhi hhigh hfJ hinj hcapPL hInter, hlow⟩

end Homeomorph
