import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Split.Marked.ShearPair
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Contact



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.Split

private abbrev E3 := EuclideanSpace Real (Fin 3)

def profileCapShift (ρ : Real → Real) (H : Real ≃ₘ[Real] Real)
    (a R : Real) (p : E3) : Real :=
  profileX ρ (H.symm (a + R ^ 2 - tangentRadiusSq p))

theorem contDiff_profileCapShift {ρ : Real → Real} (hρ : ContDiff Real ∞ ρ)
    (H : Real ≃ₘ[Real] Real) (a R : Real) : ContDiff Real ∞ (profileCapShift ρ H a R) := by
  have hs : ContDiff Real ∞ tangentRadiusSq :=
    ((EuclideanSpace.proj (𝕜 := Real) (1 : Fin 3)).contDiff.pow 2).add
      ((EuclideanSpace.proj (𝕜 := Real) (2 : Fin 3)).contDiff.pow 2)
  exact (contDiff_profileX hρ).comp (H.symm.contDiff.comp (contDiff_const.sub hs))


def profileCapShear {ρ : Real → Real} (hρ : ContDiff Real ∞ ρ)
    (H : Real ≃ₘ[Real] Real) (a R : Real) :
    Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞ where
  toFun p := p - tangentFlattenDepth p • EuclideanSpace.single 0 1 +
    profileCapShift ρ H a R p • EuclideanSpace.single 0 1
  invFun p := p + tangentFlattenDepth p • EuclideanSpace.single 0 1 -
    profileCapShift ρ H a R p • EuclideanSpace.single 0 1
  left_inv p := by
    ext i
    simp [profileCapShift, tangentFlattenDepth, tangentRadiusSq]
    ring
  right_inv p := by
    ext i
    simp [profileCapShift, tangentFlattenDepth, tangentRadiusSq]
    ring
  contMDiff_toFun :=
    ((contDiff_id.sub (contDiff_tangentFlattenDepth.smul contDiff_const)).add
      ((contDiff_profileCapShift hρ H a R).smul contDiff_const)).contMDiff
  contMDiff_invFun := by
    change ContMDiff (𝓡 3) (𝓡 3) ∞ (fun p : E3 =>
      p + tangentFlattenDepth p • EuclideanSpace.single 0 1 -
        profileCapShift ρ H a R p • EuclideanSpace.single 0 1)
    exact ((contDiff_id.add (contDiff_tangentFlattenDepth.smul contDiff_const)).sub
      ((contDiff_profileCapShift hρ H a R).smul contDiff_const)).contMDiff

theorem profileCapShear_apply {ρ : Real → Real} (hρ : ContDiff Real ∞ ρ)
    (H : Real ≃ₘ[Real] Real) (a R : Real) (p : E3) :
    profileCapShear hρ H a R p = tangentFlatShear p +
      profileCapShift ρ H a R p • EuclideanSpace.single 0 1 := rfl

@[simp] theorem profileCapShear_zero {ρ : Real → Real} (hρ : ContDiff Real ∞ ρ)
    (H : Real ≃ₘ[Real] Real) (a R : Real) (p : E3) :
    profileCapShear hρ H a R p 0 = tangentFlatShear p 0 + profileCapShift ρ H a R p := by
  rw [profileCapShear_apply]
  simp

@[simp] theorem profileCapShear_one {ρ : Real → Real} (hρ : ContDiff Real ∞ ρ)
    (H : Real ≃ₘ[Real] Real) (a R : Real) (p : E3) :
    profileCapShear hρ H a R p 1 = p 1 := by
  rw [profileCapShear_apply]
  simp

@[simp] theorem profileCapShear_two {ρ : Real → Real} (hρ : ContDiff Real ∞ ρ)
    (H : Real ≃ₘ[Real] Real) (a R : Real) (p : E3) :
    profileCapShear hρ H a R p 2 = p 2 := by
  rw [profileCapShear_apply]
  simp

theorem profileCapShear_body_nonpos {ρ : Real → Real} (hρ : ContDiff Real ∞ ρ)
    (hbound : ∀ s, |s| ≤ ρ s) (H : Real ≃ₘ[Real] Real) (a R : Real)
    {y : E3} (hy : y ∈ profileCapShear hρ H a R '' closedBall (0 : E3) 1) :
    y 0 ≤ 0 := by
  obtain ⟨p, hp, rfl⟩ := hy
  rw [profileCapShear_zero]
  exact add_nonpos (tangentFlatShear_body_nonpos (mem_image_of_mem _ hp))
    (profileX_nonpos hbound _)

theorem profileCapShear_body_inter_wall {ρ : Real → Real} (hρ : ContDiff Real ∞ ρ)
    (hbound : ∀ s, |s| ≤ ρ s) (H : Real ≃ₘ[Real] Real) (a : Real)
    (hzero : ∀ q, profileX ρ (H.symm q) = 0 ↔ a ≤ q)
    {R : Real} (hR : 0 < R) (hRsmall : R ≤ 1 / 2) :
    (profileCapShear hρ H a R '' closedBall (0 : E3) 1) ∩ {p : E3 | p 0 = 0} =
      {p : E3 | p 0 = 0 ∧ tangentRadiusSq p ≤ R ^ 2} := by
  have hRsq : R ^ 2 ≤ 1 / 4 := by nlinarith
  ext y
  constructor
  · rintro ⟨⟨p, hp, rfl⟩, hz⟩
    refine ⟨hz, ?_⟩
    have hleft := tangentFlatShear_body_nonpos (mem_image_of_mem _ hp)
    have hshift : profileCapShift ρ H a R p ≤ 0 := profileX_nonpos hbound _
    have hsum : tangentFlatShear p 0 + profileCapShift ρ H a R p = 0 := by
      change profileCapShear hρ H a R p 0 = 0 at hz
      simpa only [profileCapShear_zero] using hz
    have hshiftzero : profileCapShift ρ H a R p = 0 := by linarith
    have hs := (hzero (a + R ^ 2 - tangentRadiusSq p)).mp hshiftzero
    simp only [tangentRadiusSq, profileCapShear_one, profileCapShear_two]
    change a ≤ a + R ^ 2 - ((p 1) ^ 2 + (p 2) ^ 2) at hs
    linarith
  · rintro ⟨hy0, hys⟩
    have hm : y ∈ (tangentFlatShear '' closedBall (0 : E3) 1) ∩ {p : E3 | p 0 = 0} :=
      tangentFlatShear_body_inter_wall.symm ▸
        (show y ∈ {p : E3 | p 0 = 0 ∧ tangentRadiusSq p ≤ 1 / 4} from
          ⟨hy0, hys.trans hRsq⟩)
    obtain ⟨p, hp, hpy⟩ := hm.1
    have hs : tangentRadiusSq p = tangentRadiusSq y := by
      rw [← hpy]
      simp only [tangentRadiusSq, tangentFlatShear_one, tangentFlatShear_two]
    have hshift : profileCapShift ρ H a R p = 0 :=
      (hzero _).mpr (by rw [hs]; linarith)
    refine ⟨⟨p, hp, ?_⟩, hy0⟩
    rw [profileCapShear_apply, hshift, zero_smul, add_zero, hpy]

theorem profileCapShear_sphere_inter_wall {ρ : Real → Real} (hρ : ContDiff Real ∞ ρ)
    (hbound : ∀ s, |s| ≤ ρ s) (H : Real ≃ₘ[Real] Real) (a : Real)
    (hzero : ∀ q, profileX ρ (H.symm q) = 0 ↔ a ≤ q)
    {R : Real} (hR : 0 < R) (hRsmall : R ≤ 1 / 2) :
    (profileCapShear hρ H a R '' sphere (0 : E3) 1) ∩ {p : E3 | p 0 = 0} =
      {p : E3 | p 0 = 0 ∧ tangentRadiusSq p ≤ R ^ 2} := by
  ext y
  constructor
  · rintro ⟨hy, hy0⟩
    exact profileCapShear_body_inter_wall hρ hbound H a hzero hR hRsmall ▸
      ⟨image_mono sphere_subset_closedBall hy, hy0⟩
  · rintro ⟨hy0, hys⟩
    have hRsq : R ^ 2 ≤ 1 / 4 := by nlinarith
    have hm : y ∈ (tangentFlatShear '' sphere (0 : E3) 1) ∩ {p : E3 | p 0 = 0} :=
      tangentFlatShear_sphere_inter_wall.symm ▸
        (show y ∈ {p : E3 | p 0 = 0 ∧ tangentRadiusSq p ≤ 1 / 4} from
          ⟨hy0, hys.trans hRsq⟩)
    obtain ⟨p, hp, hpy⟩ := hm.1
    have hs : tangentRadiusSq p = tangentRadiusSq y := by
      rw [← hpy]
      simp only [tangentRadiusSq, tangentFlatShear_one, tangentFlatShear_two]
    have hshift : profileCapShift ρ H a R p = 0 :=
      (hzero _).mpr (by rw [hs]; linarith)
    refine ⟨⟨p, hp, ?_⟩, hy0⟩
    rw [profileCapShear_apply, hshift, zero_smul, add_zero, hpy]

theorem positiveSpherePatch_mem_sphere (y t : Real) (hyt : y ^ 2 + t ^ 2 ≤ 1 / 4) :
    vector (Real.sqrt (1 - (y ^ 2 + t ^ 2))) y t ∈ sphere (0 : E3) 1 := by
  have hrad : 0 ≤ 1 - (y ^ 2 + t ^ 2) := by linarith
  have hnorm : ‖vector (Real.sqrt (1 - (y ^ 2 + t ^ 2))) y t‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs,
      vector_zero, vector_one, vector_two, Real.sq_sqrt hrad]
    ring
  rw [mem_sphere_zero_iff_norm]
  nlinarith [norm_nonneg (vector (Real.sqrt (1 - (y ^ 2 + t ^ 2))) y t)]

theorem profileCapShear_positive_patch {ρ : Real → Real} (hρ : ContDiff Real ∞ ρ)
    (H : Real ≃ₘ[Real] Real) (a R y t : Real) (hyt : y ^ 2 + t ^ 2 ≤ 1 / 4) :
    profileCapShear hρ H a R (vector (Real.sqrt (1 - (y ^ 2 + t ^ 2))) y t) =
      vector (profileX ρ (H.symm (a + R ^ 2 - (y ^ 2 + t ^ 2)))) y t := by
  have hχ : tangentFlattenCutoff (y ^ 2 + t ^ 2) = 1 := by
    simp only [tangentFlattenCutoff,
      Real.smoothTransition.zero_of_nonpos (by linarith : 4 * (y ^ 2 + t ^ 2) - 1 ≤ 0),
      sub_zero]
  ext i
  fin_cases i
  · simp [profileCapShear_zero, tangentFlatShear_zero, tangentFlattenDepth,
      tangentRadiusSq, hχ, profileCapShift]
  · simp
  · simp

theorem profileCapShear_closing_slice {ρ : Real → Real} (hρ : ContDiff Real ∞ ρ)
    (H : Real ≃ₘ[Real] Real) (a R y : Real) (hy : y ^ 2 ≤ 1 / 4) :
    profileCapShear hρ H a R (vector (Real.sqrt (1 - y ^ 2)) y 0) =
      vector (profileX ρ (H.symm (a + R ^ 2 - y ^ 2))) y 0 := by
  simpa only [zero_pow (by norm_num : 2 ≠ 0), add_zero] using
    profileCapShear_positive_patch hρ H a R y 0 (by simpa using hy)


theorem exists_profile_cap_shear (H : Real ≃ₘ[Real] Real)
    {ρ : Real → Real} (hρ : ContDiff Real ∞ ρ)
    (hbound : ∀ s, |s| ≤ ρ s) (hLip : LipschitzWith 1 ρ)
    {δ : Real} (hδ : 0 < δ) (htail : ∀ s, δ ≤ |s| → ρ s = |s|)
    (hH : ∀ s, H s = profileHeight ρ s) (hmono : StrictMono H)
    {R : Real} (hR : 0 < R) (hRsmall : R ≤ 1 / 2) :
    ∃ (a : Real) (G : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞),
      0 < a ∧ a ≤ δ ∧ H a = a ∧
      (∀ q, profileX ρ (H.symm q) = 0 ↔ a ≤ q) ∧
      G = profileCapShear hρ H a R ∧
      (∀ p, G p 1 = p 1 ∧ G p 2 = p 2) ∧
      (∀ p ∈ G '' closedBall (0 : E3) 1, p 0 ≤ 0) ∧
      (G '' closedBall (0 : E3) 1) ∩ {p : E3 | p 0 = 0} =
        {p : E3 | p 0 = 0 ∧ tangentRadiusSq p ≤ R ^ 2} ∧
      (G '' sphere (0 : E3) 1) ∩ {p : E3 | p 0 = 0} =
        {p : E3 | p 0 = 0 ∧ tangentRadiusSq p ≤ R ^ 2} ∧
      ∀ y : Real, y ^ 2 ≤ 1 / 4 →
        G (vector (Real.sqrt (1 - y ^ 2)) y 0) =
          vector (profileX ρ (H.symm (a + R ^ 2 - y ^ 2))) y 0 := by
  obtain ⟨a, ha0, haδ, hHa, _, hzero⟩ :=
    exists_physical_contact_threshold H hρ hbound hLip hδ htail hH hmono
  refine ⟨a, profileCapShear hρ H a R, ha0, haδ, hHa, hzero, rfl,
    fun p => ⟨profileCapShear_one hρ H a R p, profileCapShear_two hρ H a R p⟩,
    fun _ hp => profileCapShear_body_nonpos hρ hbound H a R hp,
    profileCapShear_body_inter_wall hρ hbound H a hzero hR hRsmall,
    profileCapShear_sphere_inter_wall hρ hbound H a hzero hR hRsmall, ?_⟩
  exact fun y hy => profileCapShear_closing_slice hρ H a R y hy

end Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.Split
