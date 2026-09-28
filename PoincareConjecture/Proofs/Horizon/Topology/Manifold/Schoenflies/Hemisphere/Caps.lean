import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Hemisphere










noncomputable section
set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff RealInnerProductSpace

namespace Poincare.Manifold.Schoenflies.Hemisphere

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E] {v : E}


def capHeight (r : Real) : Real := (Real.sqrt (r ^ 2 + 1))⁻¹

theorem capHeight_pos (r : Real) : 0 < capHeight r := by
  exact inv_pos.mpr (Real.sqrt_pos.mpr (by positivity))

theorem capHeight_lt_one {r : Real} (hr : 0 < r) : capHeight r < 1 := by
  have hs : 1 < Real.sqrt (r ^ 2 + 1) := by
    rw [Real.lt_sqrt (by norm_num)]
    nlinarith
  exact (inv_lt_one₀ (by positivity)).mpr hs

theorem norm_add_center_sq (hv : ‖v‖ = 1) (x : Plane v) :
    ‖(x : E) + v‖ ^ 2 = ‖x‖ ^ 2 + 1 := by
  have hx := Submodule.mem_orthogonal_singleton_iff_inner_left.mp x.property
  simp [norm_add_sq_real, hx, hv]

theorem capHeight_lt_inner_toSphere_iff (hv : ‖v‖ = 1)
    {r : Real} (hr : 0 ≤ r) (x : Plane v) :
    capHeight r < ⟪v, (toSphere hv x : E)⟫ ↔ ‖x‖ < r := by
  rw [inner_toSphere, capHeight, inv_lt_inv₀
    (Real.sqrt_pos.mpr (by positivity)) (norm_pos_iff.mpr (add_center_ne_zero hv x))]
  have hs := Real.sq_sqrt (show 0 ≤ r ^ 2 + 1 by positivity)
  have hn := norm_add_center_sq hv x
  constructor <;> intro h <;>
    nlinarith [norm_nonneg x, norm_nonneg ((x : E) + v), Real.sqrt_nonneg (r ^ 2 + 1)]

theorem capHeight_le_inner_toSphere_iff (hv : ‖v‖ = 1)
    {r : Real} (hr : 0 ≤ r) (x : Plane v) :
    capHeight r ≤ ⟪v, (toSphere hv x : E)⟫ ↔ ‖x‖ ≤ r := by
  rw [inner_toSphere, capHeight, inv_le_inv₀
    (Real.sqrt_pos.mpr (by positivity)) (norm_pos_iff.mpr (add_center_ne_zero hv x))]
  have hs := Real.sq_sqrt (show 0 ≤ r ^ 2 + 1 by positivity)
  have hn := norm_add_center_sq hv x
  constructor <;> intro h <;>
    nlinarith [norm_nonneg x, norm_nonneg ((x : E) + v), Real.sqrt_nonneg (r ^ 2 + 1)]

theorem image_ball_toSphere (hv : ‖v‖ = 1) {r : Real} (hr : 0 ≤ r) :
    toSphere hv '' ball (0 : Plane v) r =
      {p : sphere (0 : E) 1 | capHeight r < ⟪v, (p : E)⟫} := by
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (capHeight_lt_inner_toSphere_iff hv hr x).mpr (by simpa using hx)
  · intro hp
    have hpos : 0 < ⟪v, (p : E)⟫ := (capHeight_pos r).trans hp
    have heq := toSphere_fromSphere hv p hpos
    refine ⟨fromSphere v p, ?_, heq⟩
    rw [mem_ball_zero_iff, ← capHeight_lt_inner_toSphere_iff hv hr, heq]
    exact hp

theorem image_closedBall_toSphere (hv : ‖v‖ = 1) {r : Real} (hr : 0 ≤ r) :
    toSphere hv '' closedBall (0 : Plane v) r =
      {p : sphere (0 : E) 1 | capHeight r ≤ ⟪v, (p : E)⟫} := by
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (capHeight_le_inner_toSphere_iff hv hr x).mpr (by simpa using hx)
  · intro hp
    have hpos : 0 < ⟪v, (p : E)⟫ := (capHeight_pos r).trans_le hp
    have heq := toSphere_fromSphere hv p hpos
    refine ⟨fromSphere v p, ?_, heq⟩
    rw [mem_closedBall, dist_zero_right, ← capHeight_le_inner_toSphere_iff hv hr, heq]
    exact hp


def complementRadius (c : Real) : Real := Real.sqrt (4 * (1 + c) / (1 - c))

theorem complementRadius_pos {c : Real} (hc : -1 < c) (hc1 : c < 1) :
    0 < complementRadius c := by
  apply Real.sqrt_pos.mpr
  exact div_pos (mul_pos (by norm_num) (by linarith)) (by linarith)

theorem inner_stereoInvFun (hv : ‖v‖ = 1) (x : Plane v) :
    ⟪v, (stereoInvFun hv x : E)⟫ = (‖x‖ ^ 2 - 4) / (‖x‖ ^ 2 + 4) := by
  have hx := Submodule.mem_orthogonal_singleton_iff_inner_right.mp x.property
  simp [stereoInvFun_apply, inner_add_right, inner_smul_right, hx, hv, div_eq_mul_inv,
    mul_comm]

theorem inner_stereoInvFun_le_iff (hv : ‖v‖ = 1)
    {c : Real} (hc : -1 < c) (hc1 : c < 1) (x : Plane v) :
    ⟪v, (stereoInvFun hv x : E)⟫ ≤ c ↔ ‖x‖ ≤ complementRadius c := by
  rw [inner_stereoInvFun, div_le_iff₀ (by positivity : 0 < ‖x‖ ^ 2 + 4)]
  have hden : 0 < 1 - c := by linarith
  have hnonneg : 0 ≤ 4 * (1 + c) / (1 - c) :=
    (div_pos (mul_pos (by norm_num) (by linarith)) hden).le
  have hsq := Real.sq_sqrt hnonneg
  have heq : ‖x‖ ^ 2 - 4 ≤ c * (‖x‖ ^ 2 + 4) ↔
      ‖x‖ ^ 2 ≤ 4 * (1 + c) / (1 - c) := by
    rw [le_div_iff₀ hden]
    constructor <;> intro h <;> nlinarith
  rw [heq]
  change _ ↔ ‖x‖ ≤ Real.sqrt (4 * (1 + c) / (1 - c))
  constructor <;> intro h <;>
    nlinarith [norm_nonneg x, Real.sqrt_nonneg (4 * (1 + c) / (1 - c))]

theorem image_closedBall_stereoInvFun (hv : ‖v‖ = 1)
    {c : Real} (hc : -1 < c) (hc1 : c < 1) :
    stereoInvFun hv '' closedBall (0 : Plane v) (complementRadius c) =
      {p : sphere (0 : E) 1 | ⟪v, (p : E)⟫ ≤ c} := by
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (inner_stereoInvFun_le_iff hv hc hc1 x).mpr (by simpa using hx)
  · intro hp
    change ⟪v, (p : E)⟫ ≤ c at hp
    have hps : p ∈ (stereographic hv).source := by
      intro heq
      have hpv : (p : E) = v := congrArg Subtype.val heq
      have : ⟪v, (p : E)⟫ = 1 := by rw [hpv]; simp [hv]
      linarith
    have heq : stereoInvFun hv (stereographic hv p) = p :=
      (stereographic hv).left_inv hps
    refine ⟨stereographic hv p, ?_, heq⟩
    rw [mem_closedBall, dist_zero_right, ← inner_stereoInvFun_le_iff hv hc hc1, heq]
    exact hp



theorem complement_image_ball_toSphere (hv : ‖v‖ = 1) {r : Real} (hr : 0 < r) :
    (toSphere hv '' ball (0 : Plane v) r)ᶜ =
      stereoInvFun hv '' closedBall (0 : Plane v) (complementRadius (capHeight r)) := by
  rw [image_ball_toSphere hv hr.le, image_closedBall_stereoInvFun hv
    (by linarith [capHeight_pos r]) (capHeight_lt_one hr)]
  ext p
  simp only [mem_compl_iff, mem_ofPred_eq, not_lt]

variable {n : Nat} [Fact (Module.finrank Real E = n + 1)]

theorem contMDiff_stereoInvFun (hv : ‖v‖ = 1) :
    ContMDiff 𝓘(Real, Plane v) (𝓡 n) ∞ (stereoInvFun hv) := by
  exact ((contDiff_stereoInvFunAux (v := v)).comp
    (Plane v).subtypeL.contDiff).contMDiff.codRestrict_sphere _

theorem contMDiffOn_stereographic (hv : ‖v‖ = 1) :
    ContMDiffOn (𝓡 n) 𝓘(Real, Plane v) ∞ (stereographic hv)
      (stereographic hv).source := by
  apply contDiffOn_stereoToFun.contMDiffOn.comp contMDiff_coe_sphere.contMDiffOn
  intro p hp heq
  apply hp
  apply Subtype.ext
  exact ((inner_eq_one_iff_of_norm_eq_one hv (norm_eq_of_mem_sphere p)).mp heq).symm

end Poincare.Manifold.Schoenflies.Hemisphere
