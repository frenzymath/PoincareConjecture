import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicInverseFamily
import PoincareConjecture.Proofs.M35.RawFlow.ArclengthTimeDerivative

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

variable (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
  (G : PartialStandardCapFlow g₀)
  (hrotation : ∀ t ∈ Ico 0 G.lifetime,
    ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ, ∀ x u v : StandardCapSpace,
      (G.flow.metric t).inner (standardRotation A x)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = (G.flow.metric t).inner x u v)

theorem rawInverseRadius_hasDerivAt_time {t s : ℝ}
    (ht : t ∈ Ioo 0 G.lifetime) (hs : 0 < s) :
    HasDerivAt (fun a => rawInverseRadius P G hrotation a s)
      (-intrinsicRadialVelocity (G.flow.metric t) (hrotation t ⟨ht.1.le, ht.2⟩)
          (G.complete P ⟨ht.1.le, ht.2⟩) s /
        axisRadialSpeed (G.flow.metric t) (rawInverseRadius P G hrotation t s)) t := by
  have htG : t ∈ Ico 0 G.lifetime := ⟨ht.1.le, ht.2⟩
  let q (a : ℝ) := rawInverseRadius P G hrotation a s
  let r := q t
  let S (z : ℝ × ℝ) := radialArclength (G.flow.metric z.1) z.2
  let L := fderiv ℝ S (t, r)
  let v := intrinsicRadialVelocity (G.flow.metric t) (hrotation t htG) (G.complete P htG) s
  let b := axisRadialSpeed (G.flow.metric t) r
  have hr : 0 < r := rawInverseRadius_pos P G hrotation htG hs
  have hq : DifferentiableAt ℝ q t :=
    ((rawInverseRadius_contDiffAt P G hrotation (p := (t, s)) ht).comp t
      (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  have hS : HasFDerivAt S L (t, r) :=
    ((raw_radialArclength_contDiffAt G (p := (t, r)) ht).differentiableAt (by simp)).hasFDerivAt
  have htime : L (1, 0) = v := by
    have hleft := hS.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t r))
    have hright := raw_radialArclength_hasDerivAt_velocity G ht
      (hrotation t htG) (G.complete P htG) hr.le
    rw [show radialArclength (G.flow.metric t) r = s from
      radialArclength_rawInverseRadius P G hrotation htG s] at hright
    exact hleft.unique hright
  have hspace : L (0, 1) = b := by
    have hleft := hS.comp_hasDerivAt r
      ((hasDerivAt_const r t).prodMk (hasDerivAt_id r))
    exact hleft.unique (radialArclength_hasDerivAt (G.flow.metric t) r)
  have hchain : HasDerivAt (fun a => S (a, q a)) (L (1, deriv q t)) t := by
    have hh := hS.comp_hasDerivAt t ((hasDerivAt_id t).prodMk hq.hasDerivAt)
    simpa only [Function.comp_def, id_eq] using hh
  have hconstant : HasDerivAt (fun a => S (a, q a)) 0 t := by
    apply (hasDerivAt_const t s).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds ht] with a ha
    exact radialArclength_rawInverseRadius P G hrotation ⟨ha.1.le, ha.2⟩ s
  have heq := hchain.unique hconstant
  have hlin : L (1, deriv q t) = v + deriv q t * b := by
    rw [show (1, deriv q t) = (1, 0) + deriv q t • ((0, 1) : ℝ × ℝ) by
      ext <;> simp]
    rw [map_add, map_smul, smul_eq_mul, htime, hspace]
  rw [hlin] at heq
  have hd : deriv q t = -v / b := by
    apply (eq_div_iff (axisRadialSpeed_pos (G.flow.metric t) r).ne').mpr
    linarith only [heq]
  simpa only [hd] using hq.hasDerivAt

end PoincareConjecture.M35.Uniqueness
