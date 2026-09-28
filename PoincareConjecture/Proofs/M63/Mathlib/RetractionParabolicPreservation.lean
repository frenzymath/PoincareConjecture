import PoincareConjecture.Proofs.M63.Mathlib.PeriodicVectorUniqueness
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.MetricSpace.Lipschitz

set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M63

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def retractionParabolicDefect (r : E → E)
    (A : ℝ → E → E → ℝ) (B : ℝ → E → E → E) (t : ℝ) (z v : E) : E :=
  A t z v • fderiv ℝ (fderiv ℝ r) z v v + B t z v - fderiv ℝ r z (B t z v)

theorem fderiv_retraction_comp {r : E → E} {U : Set E}
    (hU : IsOpen U) (hr : ContDiffOn ℝ 1 r U) (hmap : MapsTo r U U)
    (hid : ∀ z ∈ U, r (r z) = r z) {z : E} (hz : z ∈ U) :
    (fderiv ℝ r (r z)).comp (fderiv ℝ r z) = fderiv ℝ r z := by
  have hd (y : E) (hy : y ∈ U) : DifferentiableAt ℝ r y :=
    (hr.contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num)
  have heq : (fun y => r (r y)) =ᶠ[𝓝 z] r := by
    filter_upwards [hU.mem_nhds hz] with y hy
    exact hid y hy
  exact ((hd (r z) (hmap hz)).hasFDerivAt.comp z (hd z hz).hasFDerivAt).fderiv.symm.trans
    heq.fderiv_eq

end Normed

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem periodic_retraction_preservation
    {r : E → E} {U : Set E} {S : Set (E × E)}
    {A : ℝ → E → E → ℝ} {B : ℝ → E → E → E}
    {q qx qxx qt : ℝ → ℝ → E} {p a b alpha : ℝ} {K : NNReal}
    (hp : 0 < p) (hab : a < b) (halpha : 0 < alpha)
    (hU : IsOpen U) (hr : ContDiffOn ℝ 2 r U) (_hrmap : MapsTo r U U)
    (hq : ContinuousOn (Function.uncurry q) (univ ×ˢ Icc a b))
    (hqU : ∀ x t, t ∈ Icc a b → q x t ∈ U)
    (hper : ∀ t ∈ Icc a b, Function.Periodic (fun x => q x t) p)
    (hx : ∀ x t, t ∈ Ioo a b → HasDerivAt (fun y => q y t) (qx x t) x)
    (hxx : ∀ x t, t ∈ Ioo a b → HasDerivAt (fun y => qx y t) (qxx x t) x)
    (htime : ∀ x t, t ∈ Ioo a b → HasDerivAt (q x) (qt x t) t)
    (hA : ∀ x t, t ∈ Ioo a b → alpha ≤ A t (q x t) (qx x t))
    (hpde : ∀ x t, t ∈ Ioo a b →
      qt x t = A t (q x t) (qx x t) • qxx x t + B t (q x t) (qx x t))
    (hS : ∀ x t, t ∈ Ioo a b → (q x t, qx x t) ∈ S)
    (hproj : ∀ x t, t ∈ Ioo a b → (r (q x t), fderiv ℝ r (q x t) (qx x t)) ∈ S)
    (hLip : ∀ t ∈ Ioo a b,
      LipschitzOnWith K (fun z : E × E => retractionParabolicDefect r A B t z.1 z.2) S)
    (hcompat : ∀ x t, t ∈ Ioo a b →
      retractionParabolicDefect r A B t (r (q x t)) (fderiv ℝ r (q x t) (qx x t)) = 0)
    (hinit : ∀ x, q x a = r (q x a)) :
    ∀ x t, t ∈ Icc a b → q x t = r (q x t) := by
  let w (x t : ℝ) := q x t - r (q x t)
  let wx (x t : ℝ) := qx x t - fderiv ℝ r (q x t) (qx x t)
  let wxx (x t : ℝ) := qxx x t - (fderiv ℝ r (q x t) (qxx x t) +
    fderiv ℝ (fderiv ℝ r) (q x t) (qx x t) (qx x t))
  let wt (x t : ℝ) := qt x t - fderiv ℝ r (q x t) (qt x t)
  have hrat (x t : ℝ) (ht : t ∈ Ioo a b) : ContDiffAt ℝ 2 r (q x t) :=
    hr.contDiffAt (hU.mem_nhds (hqU x t (Ioo_subset_Icc_self ht)))
  have hrd (x t : ℝ) (ht : t ∈ Ioo a b) :
      HasFDerivAt r (fderiv ℝ r (q x t)) (q x t) :=
    ((hrat x t ht).differentiableAt (by norm_num)).hasFDerivAt
  have hw : ContinuousOn (Function.uncurry w) (univ ×ˢ Icc a b) :=
    hq.sub (hr.continuousOn.comp hq (fun z hz => hqU z.1 z.2 hz.2))
  have hwx (x t : ℝ) (ht : t ∈ Ioo a b) : HasDerivAt (fun y => w y t) (wx x t) x :=
    (hx x t ht).sub ((hrd x t ht).comp_hasDerivAt x (hx x t ht))
  have hwxx (x t : ℝ) (ht : t ∈ Ioo a b) :
      HasDerivAt (fun y => wx y t) (wxx x t) x := by
    have hd : HasFDerivAt (fderiv ℝ r) (fderiv ℝ (fderiv ℝ r) (q x t)) (q x t) :=
      (((hrat x t ht).fderiv_right (m := 1) (by norm_num)).differentiableAt
        (by norm_num)).hasFDerivAt
    have hcomp : HasDerivAt (fun y => fderiv ℝ r (q y t))
        (fderiv ℝ (fderiv ℝ r) (q x t) (qx x t)) x :=
      hd.comp_hasDerivAt x (hx x t ht)
    have happ : HasDerivAt (fun y => fderiv ℝ r (q y t) (qx y t))
        (fderiv ℝ (fderiv ℝ r) (q x t) (qx x t) (qx x t) +
          fderiv ℝ r (q x t) (qxx x t)) x := hcomp.clm_apply (hxx x t ht)
    convert! (hxx x t ht).sub happ using 1
    simp only [wxx, add_comm]
  have hwt (x t : ℝ) (ht : t ∈ Ioo a b) : HasDerivAt (w x) (wt x t) t :=
    (htime x t ht).sub ((hrd x t ht).comp_hasDerivAt t (htime x t ht))
  have herror (x t : ℝ) (ht : t ∈ Ioo a b) :
      ‖wt x t - A t (q x t) (qx x t) • wxx x t‖ ≤
        K * (‖w x t‖ + ‖wx x t‖) := by
    have heq : wt x t - A t (q x t) (qx x t) • wxx x t =
        retractionParabolicDefect r A B t (q x t) (qx x t) := by
      dsimp only [wt, wxx, retractionParabolicDefect]
      rw [hpde x t ht]
      simp only [map_add, map_smul, smul_sub, smul_add]
      abel
    rw [heq]
    have hl := (hLip t ht).dist_le_mul _ (hS x t ht) _ (hproj x t ht)
    rw [hcompat x t ht, dist_zero_right] at hl
    have hd : dist (q x t, qx x t) (r (q x t), fderiv ℝ r (q x t) (qx x t)) ≤
        ‖w x t‖ + ‖wx x t‖ := by
      rw [Prod.dist_eq, dist_eq_norm, dist_eq_norm]
      exact max_le (le_add_of_nonneg_right (norm_nonneg _))
        (le_add_of_nonneg_left (norm_nonneg _))
    exact hl.trans (mul_le_mul_of_nonneg_left hd K.2)
  have hz := periodic_vector_eq_zero_of_parabolic_bound hp hab halpha K.2 hw
    (fun t ht x => congrArg (fun z : E => z - r z) (hper t ht x)) hwx hwxx hwt hA herror
    (fun x => sub_eq_zero.mpr (hinit x))
  exact fun x t ht => sub_eq_zero.mp (hz x t ht)

end PoincareConjecture.M63
