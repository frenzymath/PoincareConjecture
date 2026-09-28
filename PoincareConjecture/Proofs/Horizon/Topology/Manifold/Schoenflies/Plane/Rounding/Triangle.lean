import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Rounding.RoundedPolygon
import Mathlib.Analysis.Convex.Between
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

open Set Function Filter
open scoped Topology ContDiff

namespace Poincare.Manifold.Schoenflies.Plane

def planeDet (u v : EuclideanSpace ℝ (Fin 2)) : ℝ := u 0 * v 1 - u 1 * v 0

theorem exists_smul_of_planeDet_eq_zero {u v : EuclideanSpace ℝ (Fin 2)}
    (hu : u ≠ 0) (hdet : planeDet u v = 0) : ∃ r : ℝ, v = r • u := by
  dsimp [planeDet] at hdet
  by_cases hu0 : u 0 = 0
  · have hu1 : u 1 ≠ 0 := by
      intro h
      apply hu
      ext i
      fin_cases i <;> simp [hu0, h]
    have hv0 : v 0 = 0 := by
      have hh : u 1 * v 0 = 0 := by rw [hu0] at hdet; nlinarith
      exact (mul_eq_zero.mp hh).resolve_left hu1
    refine ⟨v 1 / u 1, ?_⟩
    ext i
    fin_cases i <;> simp [PiLp.smul_apply, hu0, hv0, hu1]
  · refine ⟨v 0 / u 0, ?_⟩
    ext i
    fin_cases i
    · simp [PiLp.smul_apply, hu0]
    · simp only [PiLp.smul_apply, smul_eq_mul]
      change v 1 = v 0 / u 0 * u 1
      field_simp [hu0]
      nlinarith

theorem IsSimplePolygon.planeDet_triangle_ne_zero
    {p : Polygon (EuclideanSpace ℝ (Fin 2)) 3} (hp : IsSimplePolygon p) :
    planeDet (p 1 - p 0) (p 2 - p 1) ≠ 0 := by
  intro hdet
  have hu : p 1 - p 0 ≠ 0 := by
    intro h
    exact (by decide : (1 : Fin 3) ≠ 0) (hp.vertices_injective (sub_eq_zero.mp h))
  obtain ⟨r, hr⟩ := exists_smul_of_planeDet_eq_zero hu hdet
  have hcol : Collinear ℝ ({p 0, p 1, p 2} : Set (EuclideanSpace ℝ (Fin 2))) := by
    apply (collinear_iff_exists_forall_eq_smul_vadd (k := ℝ) _).mpr
    refine ⟨p 0, p 1 - p 0, ?_⟩
    intro x hx
    rcases hx with rfl | rfl | hx
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
    · rw [mem_singleton_iff] at hx
      subst x
      refine ⟨r + 1, ?_⟩
      change p 2 = (r + 1) • (p 1 - p 0) + p 0
      calc
        p 2 = (p 2 - p 1) + p 1 := by module
        _ = (r + 1) • (p 1 - p 0) + p 0 := by rw [hr]; module
  rcases hcol.wbtw_or_wbtw_or_wbtw with h | h | h
  · have heq := (hp.vertex_mem_edgeSet_iff 1 2).mp (by
      simpa [polygon_edgeSet_eq_segment] using h.symm.mem_segment)
    exact (by decide : ¬((1 : Fin 3) = 2 ∨ 1 = finRotate 3 2)) heq
  · have heq := (hp.vertex_mem_edgeSet_iff 2 0).mp (by
      simpa [polygon_edgeSet_eq_segment] using h.symm.mem_segment)
    exact (by decide : ¬((2 : Fin 3) = 0 ∨ 2 = finRotate 3 0)) heq
  · have heq := (hp.vertex_mem_edgeSet_iff 0 1).mp (by
      simpa [polygon_edgeSet_eq_segment] using h.symm.mem_segment)
    exact (by decide : ¬((0 : Fin 3) = 1 ∨ 0 = finRotate 3 1)) heq

theorem roundedCorner_radial_factor_pos {ρ : ℝ → ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hδsmall : δ < 2 / 9)
    (htail : ∀ s, δ ≤ |s| → ρ s = |s|)
    (hbound : ∀ s, |s| ≤ ρ s ∧ ρ s ≤ |s| + δ)
    (hder : ∀ s, |deriv ρ s| ≤ 1) (t : ℝ) :
    0 < 1 / 3 + (t * deriv ρ t - ρ t) / 2 := by
  by_cases ht : |t| ≤ δ
  · have hmul : |t * deriv ρ t| ≤ |t| := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (hder t) (abs_nonneg t)).trans_eq (mul_one _)
    have hlo := (abs_le.mp hmul).1
    have hρ := (hbound t).2
    linarith
  · have ht' : δ < |t| := lt_of_not_ge ht
    by_cases ht0 : 0 ≤ t
    · have hdt : δ < t := by simpa [abs_of_nonneg ht0] using ht'
      have heq : ρ =ᶠ[𝓝 t] id := by
        filter_upwards [isOpen_Ioi.mem_nhds hdt] with s hs
        have hs0 : 0 ≤ s := le_trans hδ.le hs.le
        simpa [abs_of_nonneg hs0] using htail s (by simpa [abs_of_nonneg hs0] using hs.le)
      have hd : deriv ρ t = 1 := heq.deriv_eq.trans (deriv_id t)
      rw [hd, htail t ht'.le, abs_of_nonneg ht0]
      norm_num
    · have htneg : t < 0 := lt_of_not_ge ht0
      have hdt : t < -δ := by rw [abs_of_neg htneg] at ht'; linarith
      have heq : ρ =ᶠ[𝓝 t] (fun s => -s) := by
        filter_upwards [isOpen_Iio.mem_nhds hdt] with s hs
        change s < -δ at hs
        have hs0 : s < 0 := lt_trans hs (neg_neg_of_pos hδ)
        simpa [abs_of_neg hs0] using htail s (by rw [abs_of_neg hs0]; linarith)
      have hd : deriv ρ t = -1 := heq.deriv_eq.trans (by simp)
      rw [hd, htail t ht'.le, abs_of_neg htneg]
      norm_num

theorem planeDet_roundedCorner_barycenter (a b c : EuclideanSpace ℝ (Fin 2))
    {ρ : ℝ → ℝ} {t : ℝ} (hρ : DifferentiableAt ℝ ρ t) :
    planeDet (roundedCorner ρ b (b - a) (c - b) t - (1 / 3 : ℝ) • (a + b + c))
      (deriv (roundedCorner ρ b (b - a) (c - b)) t) =
      (1 / 3 + (t * deriv ρ t - ρ t) / 2) * planeDet (b - a) (c - b) := by
  rw [(hasDerivAt_roundedCorner b (b - a) (c - b) hρ).deriv]
  simp only [planeDet, roundedCorner, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
    smul_eq_mul]
  ring

theorem hasDerivAt_roundedVertexPath {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {ρ : ℝ → ℝ} (P : ℤ → E) {δ : ℝ}
    (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (htail : ∀ s, δ ≤ |s| → ρ s = |s|)
    (hbound : ∀ s, |s| ≤ ρ s ∧ ρ s ≤ |s| + δ)
    (hρ : Differentiable ℝ ρ) (t : ℝ) :
    HasDerivAt (roundedVertexPath ρ P)
      (deriv (roundedCorner ρ (P ⌊t + 1 / 2⌋)
        (P ⌊t + 1 / 2⌋ - P (⌊t + 1 / 2⌋ - 1))
        (P (⌊t + 1 / 2⌋ + 1) - P ⌊t + 1 / 2⌋)) (t - ⌊t + 1 / 2⌋)) t := by
  let i : ℤ := ⌊t + 1 / 2⌋
  have hlo : (i : ℝ) ≤ t + 1 / 2 := Int.floor_le _
  have hhi : t + 1 / 2 < (i : ℝ) + 1 := Int.lt_floor_add_one _
  have ht : t ∈ Ioo ((i : ℝ) - 1 + δ) ((i : ℝ) + 1 - δ) := by
    constructor <;> linarith
  let Γ := roundedCorner ρ (P i) (P i - P (i - 1)) (P (i + 1) - P i)
  have hΓ := hasDerivAt_roundedCorner (P i) (P i - P (i - 1))
    (P (i + 1) - P i) (hρ (t - i))
  have hΓ' : HasDerivAt Γ (deriv Γ (t - i)) (t - i) := hΓ.congr_deriv hΓ.deriv.symm
  have htrans : HasDerivAt (fun s : ℝ => Γ (s - i)) (deriv Γ (t - i)) t := by
    simpa only [Function.comp_def, one_smul, id_eq] using
      hΓ'.scomp t ((hasDerivAt_id t).sub_const (i : ℝ))
  apply htrans.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
  exact roundedVertexPath_eq_local P hδ hδhalf htail hbound i hs

noncomputable def triangleBarycenter (p : Polygon (EuclideanSpace ℝ (Fin 2)) 3) :
    EuclideanSpace ℝ (Fin 2) := (1 / 3 : ℝ) • (p 0 + p 1 + p 2)

private theorem triangleBarycenter_eq_corner
    (p : Polygon (EuclideanSpace ℝ (Fin 2)) 3) (k : Fin 3) :
    triangleBarycenter p =
      (1 / 3 : ℝ) • (p ((finRotate 3).symm k) + p k + p (finRotate 3 k)) := by
  fin_cases k
  · change (1 / 3 : ℝ) • (p 0 + p 1 + p 2) = (1 / 3 : ℝ) • (p 2 + p 0 + p 1)
    module
  · rfl
  · change (1 / 3 : ℝ) • (p 0 + p 1 + p 2) = (1 / 3 : ℝ) • (p 1 + p 2 + p 0)
    module

private theorem planeDet_triangle_corner
    (p : Polygon (EuclideanSpace ℝ (Fin 2)) 3) (k : Fin 3) :
    planeDet (p k - p ((finRotate 3).symm k)) (p (finRotate 3 k) - p k) =
      planeDet (p 1 - p 0) (p 2 - p 1) := by
  fin_cases k
  · change planeDet (p 0 - p 2) (p 1 - p 0) = _
    simp only [planeDet, PiLp.sub_apply]
    ring
  · rfl
  · change planeDet (p 2 - p 1) (p 0 - p 2) = _
    simp only [planeDet, PiLp.sub_apply]
    ring

theorem planeDet_roundedPolygonParameter_triangle
    (p : Polygon (EuclideanSpace ℝ (Fin 2)) 3) {ρ : ℝ → ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (htail : ∀ s, δ ≤ |s| → ρ s = |s|)
    (hbound : ∀ s, |s| ≤ ρ s ∧ ρ s ≤ |s| + δ)
    (hρ : Differentiable ℝ ρ) (t : ℝ) :
    planeDet (roundedPolygonParameter ρ p t - triangleBarycenter p)
      (deriv (roundedPolygonParameter ρ p) t) =
      (1 / 3 + ((t - ⌊t + 1 / 2⌋) * deriv ρ (t - ⌊t + 1 / 2⌋) -
        ρ (t - ⌊t + 1 / 2⌋)) / 2) * planeDet (p 1 - p 0) (p 2 - p 1) := by
  let P : ℤ → EuclideanSpace ℝ (Fin 2) := fun j => p (polygonIntegerIndex 3 j)
  let i : ℤ := ⌊t + 1 / 2⌋
  let k : Fin 3 := polygonIntegerIndex 3 i
  have hprev : polygonIntegerIndex 3 (i - 1) = (finRotate 3).symm k := by
    apply (finRotate 3).injective
    rw [← polygonIntegerIndex_succ, sub_add_cancel, Equiv.apply_symm_apply]
  have hcenter : triangleBarycenter p = (1 / 3 : ℝ) • (P (i - 1) + P i + P (i + 1)) := by
    simpa only [P, hprev, polygonIntegerIndex_succ] using triangleBarycenter_eq_corner p k
  have hdet : planeDet (P i - P (i - 1)) (P (i + 1) - P i) =
      planeDet (p 1 - p 0) (p 2 - p 1) := by
    simpa only [P, hprev, polygonIntegerIndex_succ] using planeDet_triangle_corner p k
  change planeDet (roundedVertexPath ρ P t - triangleBarycenter p)
    (deriv (roundedVertexPath ρ P) t) = _
  rw [(hasDerivAt_roundedVertexPath P hδ hδhalf htail hbound hρ t).deriv, hcenter]
  change planeDet (roundedCorner ρ (P i) (P i - P (i - 1)) (P (i + 1) - P i)
    (t - i) - _) (deriv (roundedCorner ρ (P i) (P i - P (i - 1))
    (P (i + 1) - P i)) (t - i)) = _
  rw [planeDet_roundedCorner_barycenter _ _ _ (hρ (t - i)), hdet]

theorem planeDet_roundedPolygonParameter_triangle_mul_pos
    (p : Polygon (EuclideanSpace ℝ (Fin 2)) 3)
    (hp : planeDet (p 1 - p 0) (p 2 - p 1) ≠ 0) {ρ : ℝ → ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hδsmall : δ < 2 / 9)
    (htail : ∀ s, δ ≤ |s| → ρ s = |s|)
    (hbound : ∀ s, |s| ≤ ρ s ∧ ρ s ≤ |s| + δ)
    (hρ : Differentiable ℝ ρ) (hder : ∀ s, |deriv ρ s| ≤ 1) (t : ℝ) :
    0 < planeDet (roundedPolygonParameter ρ p t - triangleBarycenter p)
      (deriv (roundedPolygonParameter ρ p) t) * planeDet (p 1 - p 0) (p 2 - p 1) := by
  rw [planeDet_roundedPolygonParameter_triangle p hδ (by linarith) htail hbound hρ t]
  rw [mul_assoc, ← pow_two]
  exact mul_pos (roundedCorner_radial_factor_pos hδ hδsmall htail hbound hder _)
    (sq_pos_of_ne_zero hp)

theorem roundedPolygonParameter_triangle_ne_barycenter
    (p : Polygon (EuclideanSpace ℝ (Fin 2)) 3)
    (hp : planeDet (p 1 - p 0) (p 2 - p 1) ≠ 0) {ρ : ℝ → ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hδsmall : δ < 2 / 9)
    (htail : ∀ s, δ ≤ |s| → ρ s = |s|)
    (hbound : ∀ s, |s| ≤ ρ s ∧ ρ s ≤ |s| + δ)
    (hρ : Differentiable ℝ ρ) (hder : ∀ s, |deriv ρ s| ≤ 1) (t : ℝ) :
    roundedPolygonParameter ρ p t ≠ triangleBarycenter p := by
  intro heq
  have hpos := planeDet_roundedPolygonParameter_triangle_mul_pos p hp hδ hδsmall
    htail hbound hρ hder t
  simp [heq, planeDet] at hpos

theorem IsSimplePolygon.roundedTriangle_radial_transverse
    {p : Polygon (EuclideanSpace ℝ (Fin 2)) 3} (hp : IsSimplePolygon p)
    {ρ : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ) (hδsmall : δ < 2 / 9)
    (htail : ∀ s, δ ≤ |s| → ρ s = |s|)
    (hbound : ∀ s, |s| ≤ ρ s ∧ ρ s ≤ |s| + δ)
    (hρ : Differentiable ℝ ρ) (hder : ∀ s, |deriv ρ s| ≤ 1) (t : ℝ) :
    roundedPolygonParameter ρ p t ≠ triangleBarycenter p ∧
      0 < planeDet (roundedPolygonParameter ρ p t - triangleBarycenter p)
        (deriv (roundedPolygonParameter ρ p) t) * planeDet (p 1 - p 0) (p 2 - p 1) :=
  ⟨roundedPolygonParameter_triangle_ne_barycenter p hp.planeDet_triangle_ne_zero hδ
      hδsmall htail hbound hρ hder t,
    planeDet_roundedPolygonParameter_triangle_mul_pos p hp.planeDet_triangle_ne_zero hδ
      hδsmall htail hbound hρ hder t⟩

end Poincare.Manifold.Schoenflies.Plane
