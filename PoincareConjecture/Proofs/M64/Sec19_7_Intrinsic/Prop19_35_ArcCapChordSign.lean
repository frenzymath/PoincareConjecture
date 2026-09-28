import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ArcInwardRaySign
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CapChordSigns













noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Matrix
open Poincare.Topology.Plane.Curves Poincare.Topology.Plane.Triangles

namespace PoincareConjecture

private theorem arc_transverse_inner_ne_zero {u w : AnnulusCoordinates}
    (hind : LinearIndependent ℝ (![u, w] : Fin 2 → AnnulusCoordinates)) :
    inner ℝ (quarterTurn u) w ≠ 0 := by
  let B := basisOfLinearIndependentOfCardEqFinrank hind (by simp)
  have horth : inner ℝ (quarterTurn u) u = 0 := by
    rw [real_inner_comm]
    exact inner_quarterTurn_self _
  intro hw
  have hzero : (innerSL ℝ (quarterTurn u)).toLinearMap = 0 := by
    apply B.ext
    intro i
    fin_cases i <;>
      simp [B, coe_basisOfLinearIndependentOfCardEqFinrank, horth, hw]
  have hself : inner ℝ (quarterTurn u) (quarterTurn u) = 0 :=
    congrArg (fun f : AnnulusCoordinates →ₗ[ℝ] ℝ => f (quarterTurn u)) hzero
  have hu : u = 0 := quarterTurn.injective (by simpa only [map_zero] using
    (inner_self_eq_zero.mp hself))
  exact (hind.ne_zero (0 : Fin 2)) (by simpa using hu)





theorem m64Intrinsic_arc_cap_endpoint_chord_sign
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {T r : ℝ}
    (hinj : InjOn gamma (Icc 0 T))
    (hregular : ∀ t ∈ Ioo (0 : ℝ) T, deriv gamma t ≠ 0)
    {K U V : Set AnnulusCoordinates} (hK : IsCompact K)
    (havoid : ∀ t ∈ Ioo (0 : ℝ) T, gamma t ∉ K)
    (hU : IsOpen U) (hV : IsOpen V) (hdisj : Disjoint U V)
    (hfU : frontier U = gamma '' Icc 0 T ∪ K) (hfV : frontier V = frontier U)
    (hray : ∀ t ∈ Ioo (0 : ℝ) T, ∀ᶠ z in 𝓝[>] (0 : ℝ),
      gamma t + z • quarterTurn (deriv gamma t) ∈ U)
    (hr : 0 < r) (hrT : r < T)
    (F : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
    (hsource : {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r} ⊆ F.source)
    (hF : ContDiffOn ℝ ∞ F F.source) (hFi : ContDiffOn ℝ ∞ F.symm F.target)
    (hchord : ∀ t : ℝ, F ((1 - t) * r, t * r) =
      (1 - t) • F (r, 0) + t • F (0, r))
    (hsub : F '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r} ⊆ closure U)
    (terminal vertical : Bool)
    (haxis : ∀ s ∈ Icc (0 : ℝ) r,
      F (if vertical then (0, s) else (s, 0)) = gamma (if terminal then T - s else s)) :
    0 < inner ℝ (quarterTurn (deriv gamma (if terminal then T - r else r)))
      (if vertical then F (r, 0) - F (0, r) else F (0, r) - F (r, 0)) := by
  let b : ℝ → AnnulusCoordinates := fun s => F (if vertical then (0, s) else (s, 0))
  let beta : ℝ → AnnulusCoordinates := fun s => gamma (if terminal then T - s else s)
  let p := if terminal then T - r else r
  let d := if vertical then F (r, 0) - F (0, r) else F (0, r) - F (r, 0)
  have hp : p ∈ Ioo (0 : ℝ) T := by
    cases terminal
    · exact ⟨hr, hrT⟩
    · exact ⟨sub_pos.mpr hrT, sub_lt_self T hr⟩
  have hrI : r ∈ Icc (0 : ℝ) r := ⟨hr.le, le_rfl⟩
  have hbs : (if vertical then ((0 : ℝ), r) else (r, 0)) ∈ F.source := by
    apply hsource
    cases vertical <;> simp [hr.le]
  have hb : DifferentiableAt ℝ b r := by
    have hdF := (hF.contDiffAt (F.open_source.mem_nhds hbs)).differentiableAt (by simp)
    cases vertical
    · exact hdF.comp r (differentiableAt_id.prodMk (differentiableAt_const (0 : ℝ)))
    · exact hdF.comp r ((differentiableAt_const (0 : ℝ)).prodMk differentiableAt_id)
  have hbeta : ContDiff ℝ ∞ beta := by
    cases terminal
    · exact hg
    · exact hg.comp (contDiff_const.sub contDiff_id)
  have hderiv : deriv b r = deriv beta r := by
    rw [← hb.derivWithin (uniqueDiffOn_Icc hr r hrI),
      ← ((hbeta.differentiable (by simp)) r).derivWithin (uniqueDiffOn_Icc hr r hrI)]
    exact derivWithin_congr haxis (haxis r hrI)
  have hind : LinearIndependent ℝ (![deriv b r, d] : Fin 2 → AnnulusCoordinates) := by
    obtain ⟨hl, hr', _⟩ := cap_endpoint_transversality F hF hFi hr hsource (fun t _ => hchord t)
    cases vertical
    · exact hl
    · exact hr'
  have hnonzero : inner ℝ (quarterTurn (deriv gamma p)) d ≠ 0 := by
    have h := arc_transverse_inner_ne_zero hind
    rw [hderiv] at h
    cases terminal
    · exact h
    · simpa only [beta, p, Bool.true_eq, ite_true, deriv_comp_const_sub,
        map_neg, inner_neg_left, neg_ne_zero] using h
  have hbase : (if vertical then F (0, r) else F (r, 0)) = gamma p := by
    cases vertical <;> exact haxis r hrI
  have hwray : ∀ᶠ t in 𝓝[>] (0 : ℝ), gamma p + t • d ∈ closure U := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    cases vertical
    · apply hsub
      refine ⟨((1 - t) * r, t * r),
        ⟨mul_nonneg (sub_nonneg.mpr ht.2.le) hr.le,
          mul_nonneg ht.1.le hr.le, by dsimp; nlinarith⟩, ?_⟩
      rw [hchord, ← hbase]
      dsimp [d]
      module
    · apply hsub
      refine ⟨((1 - (1 - t)) * r, (1 - t) * r),
        ⟨by nlinarith [mul_nonneg ht.1.le hr.le],
          mul_nonneg (sub_nonneg.mpr ht.2.le) hr.le, by dsimp; nlinarith⟩, ?_⟩
      rw [hchord, ← hbase]
      dsimp [d]
      module
  exact m64Intrinsic_arc_inward_ray_transverse_pos hg hinj hp hregular hK (havoid p hp)
    hU hV hdisj hfU hfV (hray p hp) hnonzero hwray

end PoincareConjecture
