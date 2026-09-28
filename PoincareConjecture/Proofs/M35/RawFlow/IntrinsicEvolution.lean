import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicInverseTime
import PoincareConjecture.Proofs.M35.RawFlow.AxisAngularRicci

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

noncomputable def rawWarpingRadius (t s : ℝ) : ℝ :=
  axisWarpingRadius (G.flow.metric t) (rawInverseRadius P G hrotation t s)

noncomputable def rawRadialVelocity (t s : ℝ) : ℝ :=
  if ht : t ∈ Ico 0 G.lifetime then
    intrinsicRadialVelocity (G.flow.metric t) (hrotation t ht) (G.complete P ht) s
  else 0

theorem rawWarpingRadius_eq {t : ℝ} (ht : t ∈ Ico 0 G.lifetime) :
    rawWarpingRadius P G hrotation t =
      intrinsicWarpingRadius (G.flow.metric t) (hrotation t ht) (G.complete P ht) := by
  funext s
  rw [rawWarpingRadius, rawInverseRadius_eq P G hrotation ht]
  rfl

theorem rawRadialVelocity_eq {t : ℝ} (ht : t ∈ Ico 0 G.lifetime) :
    rawRadialVelocity P G hrotation t =
      intrinsicRadialVelocity (G.flow.metric t) (hrotation t ht) (G.complete P ht) := by
  funext s
  simp only [rawRadialVelocity, dif_pos ht]

theorem rawWarpingRadius_contDiffAt {p : ℝ × ℝ} (hp : p.1 ∈ Ioo 0 G.lifetime) :
    ContDiffAt ℝ ∞ (Function.uncurry (rawWarpingRadius P G hrotation)) p := by
  have hn : Ico 0 G.lifetime ×ˢ (univ : Set ℝ) ∈
      𝓝 (p.1, rawInverseRadius P G hrotation p.1 p.2) :=
    prod_mem_nhds (Ico_mem_nhds hp.1 hp.2) univ_mem
  have hA := (raw_axisWarpingRadius_contDiffOn G).contDiffAt hn
  exact hA.comp p (contDiffAt_fst.prodMk (rawInverseRadius_contDiffAt P G hrotation hp))

theorem rawWarpingRadius_contDiffOn :
    ContDiffOn ℝ ∞ (Function.uncurry (rawWarpingRadius P G hrotation))
      (Ioo 0 G.lifetime ×ˢ univ) :=
  fun _ hp => (rawWarpingRadius_contDiffAt P G hrotation hp.1).contDiffWithinAt

theorem rawWarpingRadius_hasDerivAt {t s : ℝ} (ht : t ∈ Ico 0 G.lifetime)
    (hs : 0 < s) : HasDerivAt (rawWarpingRadius P G hrotation t)
      (axisWarpingSlope (G.flow.metric t) (rawInverseRadius P G hrotation t s)) s := by
  rw [rawWarpingRadius_eq P G hrotation ht, rawInverseRadius_eq P G hrotation ht]
  exact intrinsicWarpingRadius_hasDerivAt (G.flow.metric t) (hrotation t ht)
    (G.complete P ht) hs

theorem rawWarpingRadius_deriv_hasDerivAt {t s : ℝ} (ht : t ∈ Ico 0 G.lifetime)
    (hs : 0 < s) : HasDerivAt (deriv (rawWarpingRadius P G hrotation t))
      (axisWarpingSecond (G.flow.metric t) (rawInverseRadius P G hrotation t s)) s := by
  rw [rawWarpingRadius_eq P G hrotation ht, rawInverseRadius_eq P G hrotation ht]
  exact intrinsicWarpingRadius_deriv_hasDerivAt (G.flow.metric t) (hrotation t ht)
    (G.complete P ht) hs

theorem rawWarpingRadius_hasDerivAt_time {t s : ℝ}
    (ht : t ∈ Ioo 0 G.lifetime) (hs : 0 < s) :
    HasDerivAt (fun a => rawWarpingRadius P G hrotation a s)
      (deriv (deriv (rawWarpingRadius P G hrotation t)) s +
        (deriv (rawWarpingRadius P G hrotation t) s ^ 2 - 1) /
          rawWarpingRadius P G hrotation t s -
        rawRadialVelocity P G hrotation t s * deriv (rawWarpingRadius P G hrotation t) s) t := by
  have htG : t ∈ Ico 0 G.lifetime := ⟨ht.1.le, ht.2⟩
  let q (a : ℝ) := rawInverseRadius P G hrotation a s
  let r := q t
  let A (z : ℝ × ℝ) := axisWarpingRadius (G.flow.metric z.1) z.2
  let L := fderiv ℝ A (t, r)
  let v := rawRadialVelocity P G hrotation t s
  let b := axisRadialSpeed (G.flow.metric t) r
  let p := axisWarpingSlope (G.flow.metric t) r
  let k := axisWarpingSecond (G.flow.metric t) r
  have hr : 0 < r := rawInverseRadius_pos P G hrotation htG hs
  have hA : HasFDerivAt A L (t, r) :=
    (((raw_axisWarpingRadius_contDiffOn G).contDiffAt
      (prod_mem_nhds (Ico_mem_nhds ht.1 ht.2) univ_mem)).differentiableAt
        (by simp)).hasFDerivAt
  have htime : L (1, 0) = k + (p ^ 2 - 1) / A (t, r) := by
    have hleft := hA.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t r))
    have hright := (raw_axisWarpingRadius_hasDerivWithinAt_intrinsic G htG
      (hrotation t htG) hr).hasDerivAt (Ico_mem_nhds ht.1 ht.2)
    exact hleft.unique hright
  have hspace : L (0, 1) = b * p := by
    have hleft := hA.comp_hasDerivAt r
      ((hasDerivAt_const r t).prodMk (hasDerivAt_id r))
    exact hleft.unique (axisWarpingRadius_hasDerivAt (G.flow.metric t) hr)
  have hq : HasDerivAt q (-v / b) t := by
    simpa only [v, rawRadialVelocity_eq P G hrotation htG] using
      rawInverseRadius_hasDerivAt_time P G hrotation ht hs
  have hchain : HasDerivAt (fun a => rawWarpingRadius P G hrotation a s)
      (L (1, -v / b)) t := by
    have hh := hA.comp_hasDerivAt t ((hasDerivAt_id t).prodMk hq)
    simpa only [Function.comp_def, id_eq, A, q, rawWarpingRadius] using hh
  have hlin : L (1, -v / b) = k + (p ^ 2 - 1) / A (t, r) - v * p := by
    rw [show (1, -v / b) = (1, 0) + (-v / b) • ((0, 1) : ℝ × ℝ) by
      ext <;> simp]
    rw [map_add, map_smul, smul_eq_mul, htime, hspace]
    have hb : b ≠ 0 := (axisRadialSpeed_pos (G.flow.metric t) r).ne'
    field_simp [hb]
    ring
  rw [hlin] at hchain
  rw [(rawWarpingRadius_hasDerivAt P G hrotation htG hs).deriv,
    (rawWarpingRadius_deriv_hasDerivAt P G hrotation htG hs).deriv]
  exact hchain

end PoincareConjecture.M35.Uniqueness
