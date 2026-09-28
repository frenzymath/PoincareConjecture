import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Conjugate.Variation.Energy
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Conjugate.Variation.Density
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture.M28.EndpointVariation

open ConjugateVariation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def position (q v : ℝ → E) (a b : ℝ) (p : ℝ × ℝ) : E :=
  q p.2 + ((p.2 - a) / (b - a)) • v p.1

def velocity (w v : ℝ → E) (a b : ℝ) (p : ℝ × ℝ) : E :=
  w p.2 + (b - a)⁻¹ • v p.1

def density (G : E → E →L[ℝ] E →L[ℝ] ℝ)
    (q w v : ℝ → E) (a b : ℝ) (p : ℝ × ℝ) : ℝ :=
  (1 / 2 : ℝ) * G (position q v a b p)
    (velocity w v a b p) (velocity w v a b p)

theorem hasDerivAt_position_time {q w v : ℝ → E} {a b s t : ℝ}
    (hq : HasDerivAt q (w t) t) :
    HasDerivAt (fun r => position q v a b (s, r))
      (velocity w v a b (s, t)) t := by
  have h := hq.add
    ((((hasDerivAt_id t).sub_const a).div_const (b - a)).smul_const (v s))
  have heq : (q + fun y => ((y - a) / (b - a)) • v s) =
      (fun r => position q v a b (s, r)) := by
    funext r
    rfl
  simp only [id_eq] at h
  rw [heq] at h
  simpa only [velocity, one_div] using h

theorem contDiffOn_position {q v : ℝ → E} {a b : ℝ} {I J : Set ℝ}
    (hq : ContDiffOn ℝ 1 q J) (hv : ContDiffOn ℝ 1 v I) :
    ContDiffOn ℝ 1 (position q v a b) (I ×ˢ J) := by
  exact (hq.comp contDiffOn_snd (fun _ h => h.2)).add
    (((contDiffOn_snd.sub contDiffOn_const).div_const (b - a)).smul
      (hv.comp contDiffOn_fst (fun _ h => h.1)))

theorem contDiffOn_velocity {w v : ℝ → E} {a b : ℝ} {I J : Set ℝ}
    (hw : ContDiffOn ℝ 1 w J) (hv : ContDiffOn ℝ 1 v I) :
    ContDiffOn ℝ 1 (velocity w v a b) (I ×ˢ J) := by
  exact (hw.comp contDiffOn_snd (fun _ h => h.2)).add
    (contDiffOn_const.smul (hv.comp contDiffOn_fst (fun _ h => h.1)))

private theorem hasDerivAt_metricEnergy_displacement
    {G : E → E →L[ℝ] E →L[ℝ] ℝ}
    {Γ : E → E →L[ℝ] E →L[ℝ] E} {x w V : E} {v : ℝ → E} {c k : ℝ}
    (hG : DifferentiableAt ℝ G x)
    (hsymm : ∀ Y Z, G x Y Z = G x Z Y)
    (hcompat : IsMetricCompatibleAt G Γ x)
    (hv : HasDerivAt v V 0) (hv0 : v 0 = 0) :
    HasDerivAt (fun s => (1 / 2 : ℝ) *
      G (x + c • v s) (w + k • v s) (w + k • v s))
      (G x (Γ x (c • V) w + k • V) w) 0 := by
  have hx : HasDerivAt (fun s => x + c • v s) (c • V) 0 := by
    have h := (hasDerivAt_const 0 x).add (hv.const_smul c)
    have heq : ((fun _ : ℝ => x) + c • v) = (fun s => x + c • v s) := by
      funext s
      rfl
    rw [heq] at h
    simpa only [zero_add] using h
  have hw : HasDerivAt (fun s => w + k • v s) (k • V) 0 := by
    have h := (hasDerivAt_const 0 w).add (hv.const_smul k)
    have heq : ((fun _ : ℝ => w) + k • v) = (fun s => w + k • v s) := by
      funext s
      rfl
    rw [heq] at h
    simpa only [zero_add] using h
  have hcoef : HasDerivAt (fun s => G (x + c • v s))
      (fderiv ℝ G x (c • V)) 0 := by
    have hG' : DifferentiableAt ℝ G (x + c • v 0) := by
      simpa only [hv0, smul_zero, add_zero] using hG
    have h := HasFDerivAt.comp_hasDerivAt (l := G)
      (f := fun s => x + c • v s) 0 hG'.hasFDerivAt hx
    have heq : (G ∘ fun s => x + c • v s) = (fun s => G (x + c • v s)) := by
      funext s
      rfl
    rw [heq] at h
    simpa only [hv0, smul_zero, add_zero] using h
  have he := ((hcoef.clm_apply hw).clm_apply hw).const_mul (1 / 2 : ℝ)
  convert he using 1 <;> try rfl
  simp only [hv0, smul_zero, add_zero, _root_.add_apply]
  rw [hcompat (c • V) w w,
    hsymm w (Γ x (c • V) w), hsymm w (k • V)]
  simp only [map_add, _root_.add_apply]
  ring

private theorem hasDerivAt_pairing_geodesic
    {G : E → E →L[ℝ] E →L[ℝ] ℝ}
    {Γ : E → E →L[ℝ] E →L[ℝ] E}
    {q w Y : ℝ → E} {Z : E} {t : ℝ}
    (hG : DifferentiableAt ℝ G (q t))
    (hcompat : IsMetricCompatibleAt G Γ (q t))
    (hq : HasDerivAt q (w t) t)
    (hw : HasDerivAt w (-Γ (q t) (w t) (w t)) t)
    (hY : HasDerivAt Y Z t) :
    HasDerivAt (fun s => G (q s) (Y s) (w s))
      (G (q t) (Γ (q t) (w t) (Y t) + Z) (w t)) t := by
  have hcoef : HasDerivAt (fun s => G (q s))
      (fderiv ℝ G (q t) (w t)) t := by
    have h := HasFDerivAt.comp_hasDerivAt (l := G) (f := q) t hG.hasFDerivAt hq
    have heq : G ∘ q = (fun s => G (q s)) := by
      funext s
      rfl
    rw [heq] at h
    exact h
  have h := (hcoef.clm_apply hY).clm_apply hw
  convert h using 1 <;> try rfl
  simp only [_root_.add_apply, map_neg, map_add]
  rw [hcompat (w t) (Y t) (w t)]
  ring

theorem hasDerivAt_integral_density
    {G : E → E →L[ℝ] E →L[ℝ] ℝ}
    {Γ : E → E →L[ℝ] E →L[ℝ] E}
    {q w v : ℝ → E} {a b r : ℝ} {Ω : Set E}
    (hab : a < b) (hr : 0 < r) (hΩ : IsOpen Ω)
    (hG : ContDiffOn ℝ 1 G Ω)
    (hq : ContDiffOn ℝ 1 q (Ioo (a - r) (b + r)))
    (hw : ContDiffOn ℝ 1 w (Ioo (a - r) (b + r)))
    (hv : ContDiffOn ℝ 1 v (Ioo (-r) r)) (hv0 : v 0 = 0)
    (hmap : MapsTo (position q v a b)
      (Ioo (-r) r ×ˢ Ioo (a - r) (b + r)) Ω)
    (hqderiv : ∀ t ∈ Icc a b, HasDerivAt q (w t) t)
    (hwderiv : ∀ t ∈ Icc a b, HasDerivAt w (-Γ (q t) (w t) (w t)) t)
    (hsymm : ∀ t ∈ Icc a b, ∀ Y Z, G (q t) Y Z = G (q t) Z Y)
    (hcompat : ∀ t ∈ Icc a b, IsMetricCompatibleAt G Γ (q t))
    (hΓsymm : ∀ t ∈ Icc a b, ∀ Y Z, Γ (q t) Y Z = Γ (q t) Z Y) :
    HasDerivAt (fun s => ∫ t in a..b, density G q w v a b (s, t))
      (G (q b) (deriv v 0) (w b)) 0 := by
  let I := Ioo (-r) r
  let J := Ioo (a - r) (b + r)
  have h0 : (0 : ℝ) ∈ I := ⟨by linarith, hr⟩
  have hsub : Icc a b ⊆ J := by
    intro t ht
    change a - r < t ∧ t < b + r
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hqmap : MapsTo q J Ω := by
    intro t ht
    simpa only [position, hv0, smul_zero, add_zero] using
      @hmap (0, t) ⟨h0, ht⟩
  have hGq : ContDiffOn ℝ 1 (fun t => G (q t)) J := hG.comp hq hqmap
  have hpos : ContDiffOn ℝ 1 (position q v a b) (I ×ˢ J) :=
    contDiffOn_position hq hv
  have hvel : ContDiffOn ℝ 1 (velocity w v a b) (I ×ˢ J) :=
    contDiffOn_velocity hw hv
  have he : ContDiffOn ℝ 1 (density G q w v a b) (I ×ˢ J) :=
    contDiffOn_const.mul (((hG.comp hpos hmap).clm_apply hvel).clm_apply hvel)
  have he' : ContDiffOn ℝ 1
      (Function.uncurry fun s t => density G q w v a b (s, t)) (I ×ˢ J) := by
    apply he.congr
    rintro ⟨s, t⟩ _
    rfl
  have hE := hasDerivAt_intervalIntegral_of_contDiffOn_box
    (F := fun s t => density G q w v a b (s, t)) (s₀ := 0) hab.le hr
    (by simpa only [zero_sub, zero_add, I, J] using he') (s := 0)
    (show (0 : ℝ) ∈ Ioo (0 - r) (0 + r) by simpa only [zero_sub, zero_add] using h0)
  let V := deriv v 0
  let Y : ℝ → E := fun t => ((t - a) / (b - a)) • V
  let B : ℝ → ℝ := fun t => G (q t) (Y t) (w t)
  let D : ℝ → ℝ := fun t => G (q t)
    (Γ (q t) (w t) (Y t) + (b - a)⁻¹ • V) (w t)
  have hY : ContDiff ℝ 1 Y :=
    ((contDiff_id.sub contDiff_const).div_const (b - a)).smul contDiff_const
  have hB : ContDiffOn ℝ 1 B J :=
    (hGq.clm_apply hY.contDiffOn).clm_apply hw
  have hV : HasDerivAt v V 0 :=
    ((hv.contDiffAt (isOpen_Ioo.mem_nhds h0)).differentiableAt (by norm_num)).hasDerivAt
  have hDG (t : ℝ) (ht : t ∈ Icc a b) : DifferentiableAt ℝ G (q t) :=
    (hG.contDiffAt (hΩ.mem_nhds (hqmap (hsub ht)))).differentiableAt (by norm_num)
  have hBderiv (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt B (D t) t := by
    apply hasDerivAt_pairing_geodesic (hDG t ht) (hcompat t ht)
      (hqderiv t ht) (hwderiv t ht)
    simpa only [Y, one_div, id_eq] using
      (((hasDerivAt_id t).sub_const a).div_const (b - a)).smul_const V
  have hpartial (t : ℝ) (ht : t ∈ Icc a b) :
      HasDerivAt (fun s => density G q w v a b (s, t)) (D t) 0 := by
    have h := hasDerivAt_metricEnergy_displacement (hDG t ht)
      (hsymm t ht) (hcompat t ht) hV hv0
      (w := w t) (c := (t - a) / (b - a)) (k := (b - a)⁻¹)
    simpa only [density, position, velocity, D, Y,
      hΓsymm t ht (((t - a) / (b - a)) • V) (w t)] using h
  have hDcont : ContinuousOn D (Icc a b) := by
    apply ((hB.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl).mono hsub).congr
    intro t ht
    exact (hBderiv t ht).deriv.symm
  have hint : IntervalIntegrable D volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hab.le] using hDcont
  have hFTC : (∫ t in a..b, D t) = B b - B a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hBderiv t (by simpa only [uIcc_of_le hab.le] using ht)) hint
  have hintegral : (∫ t in a..b,
      deriv (fun s => density G q w v a b (s, t)) 0) = G (q b) V (w b) := by
    rw [intervalIntegral.integral_congr (fun t ht =>
      (hpartial t (by simpa only [uIcc_of_le hab.le] using ht)).deriv), hFTC]
    simp only [B, Y, sub_self, zero_div, zero_smul, map_zero, zero_apply,
      div_self (sub_ne_zero.mpr hab.ne'), one_smul, sub_zero]
  rw [hintegral] at hE
  exact hE

end PoincareConjecture.M28.EndpointVariation
