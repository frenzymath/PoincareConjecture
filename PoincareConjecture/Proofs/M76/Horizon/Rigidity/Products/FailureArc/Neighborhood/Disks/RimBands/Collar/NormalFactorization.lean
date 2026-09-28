import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Orientation.AffineBoundarySign
import PoincareConjecture.Proofs.M76.Brown.NormalTransitionSigns

set_option autoImplicit false

open Set Geometry SignType

namespace PoincareConjecture.M76.Dehn.Annuli.RimBands

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)

theorem plLocalSign_eq_tangent_mul_normalTransitionSign
    (h : OpenPartialHomeomorph C3 C3)
    (hh : h ∈ piecewiseAffineGroupoid C3)
    (hpair : ∀ z ∈ h.source, (h z).2 = 0 ↔ z.2 = 0)
    (A : P2 ≃ᴬ[ℝ] P2)
    (htangent : ∀ z ∈ h.source, z.2 = 0 → h z = (A z.1, 0))
    (p : {p : P2 // (p, (0 : ℝ)) ∈ h.source}) :
    plLocalSign h hh ⟨(p, 0), p.property⟩ =
      SignType.sign (LinearMap.det A.toContinuousAffineMap.toAffineMap.linear) *
        BrownCollar.normalTransitionSign h hpair p := by
  let s := BrownCollar.normalTransitionSign h hpair p
  obtain ⟨hs, U, hU, hpU, hUs, hsign⟩ :=
    BrownCollar.normalTransitionSign_spec h hpair p
  change s ≠ 0 at hs
  let c : ℝ := SignType.cast s
  have hcsign : SignType.sign c = s := by
    cases hs' : s <;> norm_num [c, hs', SignType.cast, sign_apply]
  have hcsq : c * c = 1 := by
    cases hs' : s with
    | zero => exact False.elim (hs hs')
    | neg => norm_num [c, hs', SignType.cast]
    | pos => norm_num [c, hs', SignType.cast]
  have hssq : s * s = 1 := mul_inv_cancel₀ hs
  let ell : C3 →ᴬ[ℝ] ℝ := (ContinuousLinearMap.snd ℝ P2 ℝ).toContinuousAffineMap
  let m : C3 →ᴬ[ℝ] ℝ := c • ell
  let n : C3 := (0, 1)
  let n' : C3 := (0, c)
  let B : C3 →ᴬ[ℝ] C3 := A.toContinuousAffineMap.prodMap
    (ContinuousAffineMap.const ℝ ℝ 0)
  let r := h.restr U
  have hr : r ∈ piecewiseAffineGroupoid C3 := closedUnderRestriction' hh hU
  have hpr : ((p : P2), (0 : ℝ)) ∈ r.source :=
    ⟨p.property, by simpa only [hU.interior_eq] using hpU⟩
  have hside : ∀ z ∈ r.source, 0 ≤ m (r z) ↔ 0 ≤ ell z := by
    intro z hz
    have heq : SignType.sign (c * (h z).2) = SignType.sign z.2 := by
      rw [sign_mul, hcsign, hsign z (interior_subset hz.2),
        ← mul_assoc, hssq, one_mul]
    exact (sign_nonneg_iff).symm.trans
      ((congrArg (fun a : SignType => 0 ≤ a) heq).to_iff.trans
        sign_nonneg_iff)
  have hB : ∀ z, ell z = 0 → m (B z) = 0 := by
    intro z _
    change c * 0 = 0
    exact mul_zero _
  have hBi : InjOn B {z | ell z = 0} := by
    intro z hz w hw heq
    apply Prod.ext
    · exact A.injective (congrArg Prod.fst heq)
    · exact hz.trans hw.symm
  have hlocal := plLocalSign_eq_affineNormalExtension r hr ell m n n' B
    (by rfl) (by exact hcsq) hB hBi hside
    (fun z hz hz0 => htangent z hz.1 hz0) ⟨(p, 0), hpr⟩ rfl
  have hlinear : (affineNormalExtension ell n n' B).toAffineMap.linear =
      LinearMap.prodMap A.toContinuousAffineMap.toAffineMap.linear
        (c • LinearMap.id : ℝ →ₗ[ℝ] ℝ) := by
    apply LinearMap.ext
    intro z
    change (affineNormalExtension ell n n' B).contLinear z = _
    have hv := (affineNormalExtension ell n n' B).contLinear_map_vsub z 0
    simp only [vsub_eq_sub, sub_zero] at hv
    rw [hv]
    simp [affineNormalExtension_apply, ell, n, n', B, sub_eq_add_neg]
    constructor
    · simpa [vsub_eq_sub, sub_eq_add_neg] using
        (A.toContinuousAffineMap.contLinear_map_vsub z.1 0).symm
    · exact mul_comm _ _
  rw [hlinear, LinearMap.det_prodMap, LinearMap.det_ring] at hlocal
  simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul, mul_one,
    sign_mul, hcsign] at hlocal
  exact (plLocalSign_restr h hh hU ⟨(p, 0), hpr⟩).symm.trans hlocal

end PoincareConjecture.M76.Dehn.Annuli.RimBands
