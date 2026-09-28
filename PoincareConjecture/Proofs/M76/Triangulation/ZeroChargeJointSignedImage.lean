import PoincareConjecture.Proofs.M76.Triangulation.ZeroChargeJointCylinder
import PoincareConjecture.Proofs.M76.Triangulation.ZeroChargeJointComposition

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.ZeroChargeJoint

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem image_eq_of_signed_joint_finitePL
    {N : Set E} (hN : FinitePiecewiseAffineOn (id : E → E) N)
    (hconn : IsConnected (interior N)) {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (H : E × ℝ → E) (hH : FinitePiecewiseAffineOn H (N ×ˢ Icc (-epsilon) epsilon))
    (hinj : ∀ t ∈ Icc (-epsilon) epsilon, InjOn (fun x => H (x, t)) N)
    (hfix : ∀ t ∈ Icc (-epsilon) epsilon,
      EqOn (fun x => H (x, t)) id (frontier N))
    (hzero : EqOn (fun x => H (x, 0)) id N) :
    ∀ t ∈ Icc (-epsilon) epsilon, (fun x => H (x, t)) '' N = N := by
  intro t ht
  have htime (s : ℝ) (hs : s ∈ Icc 0 1) : s * t ∈ Icc (-epsilon) epsilon := by
    have hup := mul_nonneg hs.1 (sub_nonneg.mpr ht.2)
    have hlo := mul_nonneg hs.1 (sub_nonneg.mpr ht.1)
    have hrest := mul_nonneg (sub_nonneg.mpr hs.2) hepsilon
    constructor <;> nlinarith
  have hpath (x : E) (hx : x ∈ N) :
      ContinuousOn (fun s : ℝ => H (x, s * t)) (Icc 0 1) :=
    hH.continuousOn.comp
      (continuous_const.prodMk (continuous_id.mul continuous_const)).continuousOn
      (fun s hs => ⟨hx, htime s hs⟩)
  have hPL (s : ℝ) (hs : s ∈ Icc 0 1) :
      FinitePiecewiseAffineOn (fun x => H (x, s * t)) N := by
    have hinput : FinitePiecewiseAffineOn (fun x : E => (x, s * t)) N :=
      hN.postcomp ((ContinuousAffineMap.id ℝ E).prod
        (ContinuousAffineMap.const ℝ E (s * t)))
    exact hH.comp hinput (fun x hx => ⟨hx, htime s hs⟩)
  have hrange := image_eq_of_boundary_fixed_finitePL_homotopy hN.isCompact hconn
    (show (0 : ℝ) ≤ 1 by norm_num) (fun s x => H (x, s * t)) hpath hPL
    (fun s hs => hinj _ (htime s hs)) (fun s hs => hfix _ (htime s hs))
    (by simpa only [zero_mul] using hzero)
  simpa only [one_mul] using hrange 1 ⟨zero_le_one, le_rfl⟩

end PoincareConjecture.M76.ZeroChargeJoint
