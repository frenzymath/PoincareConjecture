import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.FreePhaseVerticalEnergy
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.TwoCircleObservation









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Topology
open scoped ContDiff Manifold

namespace PoincareConjecture

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)




theorem M64FreeWeakPhaseAnnulus.exists_strict_modulus_interval
    {R : EuclideanSpace ℝ (Fin m) →L[ℝ] LoopPlane} {H0 H1 : ℝ ≃o ℝ} {k D : ℝ}
    (hk : k ≠ 0) (hD : D ≠ 0)
    (hH0 : ∀ x, H0 (x + curvePeriod) = H0 x + D)
    (hH1 : ∀ x, H1 (x + curvePeriod) = H1 x + D)
    (hc0 : Continuous (e ∘ c0)) (hc1 : Continuous (e ∘ c1))
    (T : E →L[ℝ] ℝ) {v0 v1 : ℝ} (hne : v0 ≠ v1)
    (h0 : ∀ x, T (e (c0 x)) = v0) (h1 : ∀ x, T (e (c1 x)) = v1)
    (B : M → E →L[ℝ] E →L[ℝ] ℝ) (hB : Continuous B)
    (hei : IsEmbedding e) {K : ℝ} (hb : ∀ q, ‖B q‖ ≤ K)
    (hpos : ∀ q v, 0 ≤ B q v v) {C : ℝ}
    (hcoercive : ∀ (q : M) (v : E), v ∈ range (mfderiv (𝓡 n) (𝓡 m) e q) →
      ‖v‖ ^ 2 ≤ C * B q v v)
    {cap : ℝ} (hcap : 0 < cap) :
    ∃ lo hi : ℝ, 0 < lo ∧ lo < hi ∧
      ∀ A : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k D,
        ∀ r : ℝ, 0 < r → A.annulus.weightedEnergy B r ≤ cap → r ∈ Ioo lo hi := by
  let alpha := D ^ 2 / (2 * curvePeriod * max ((‖R‖ ^ 2 / k ^ 2) * C) 1)
  let beta := curvePeriod * (v1 - v0) ^ 2 / (2 * max (‖T‖ ^ 2 * C) 1)
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  have halpha : 0 < alpha := div_pos (sq_pos_of_ne_zero hD)
    (mul_pos (mul_pos (by norm_num) hP) (lt_max_of_lt_right zero_lt_one))
  have hbeta : 0 < beta := div_pos
    (mul_pos hP (sq_pos_of_ne_zero (sub_ne_zero.mpr hne.symm)))
    (mul_pos (by norm_num) (lt_max_of_lt_right zero_lt_one))
  have hlevel : 0 < cap + 1 := by linarith
  let lo := beta / (cap + 1)
  let hi := max ((cap + 1) / alpha) (lo + 1)
  have hlo : 0 < lo := div_pos hbeta hlevel
  refine ⟨lo, hi, hlo, (lt_add_one lo).trans_le (le_max_right _ _), ?_⟩
  intro A r hr henergy
  have hh : alpha * r ≤ cap := by
    have hh := (A.weightedEnergy_ge_degree hk B hB hei hb hpos hcoercive hr).trans henergy
    calc
      alpha * r = r * D ^ 2 / (2 * curvePeriod * max ((‖R‖ ^ 2 / k ^ 2) * C) 1) := by
        dsimp only [alpha]
        ring
      _ ≤ cap := hh
  have hv : beta * r⁻¹ ≤ cap := by
    have hv := (A.weightedEnergy_ge_boundary_reader hH0 hH1 hc0 hc1 T h0 h1
      B hB hei hb hpos hcoercive hr).trans henergy
    calc
      beta * r⁻¹ = r⁻¹ * curvePeriod * (v1 - v0) ^ 2 / (2 * max (‖T‖ ^ 2 * C) 1) := by
        dsimp only [beta]
        ring
      _ ≤ cap := hv
  have hlow : lo < r := by
    apply (div_lt_iff₀ hlevel).mpr
    have hh := mul_lt_mul_of_pos_right (hv.trans_lt (lt_add_one cap)) hr
    have heq : beta * r⁻¹ * r = beta := by field_simp
    rw [heq] at hh
    simpa only [mul_comm] using hh
  have hupp : r < (cap + 1) / alpha := by
    apply (lt_div_iff₀ halpha).mpr
    simpa only [mul_comm] using hh.trans_lt (lt_add_one cap)
  exact ⟨hlow, hupp.trans_le (le_max_left _ _)⟩

namespace M64

variable [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference auxiliary : ℝ}




theorem auxiliaryCircle_freeWeakPhase_confined
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary)
    (e : Q.charts.Point → EuclideanSpace ℝ (Fin m)) (he : Continuous e)
    (R T : EuclideanSpace ℝ (Fin m) →L[ℝ] LoopPlane)
    (hT : ∀ q, T (e q) = planarCircleObservation q.2)
    (gamma0 gamma1 : ℝ → P.charts.Point) (hc0 : Continuous gamma0) (hc1 : Continuous gamma1)
    {q0 q1 : Q.circle.Point} (hne : q0 ≠ q1)
    (H0 H1 : ℝ ≃o ℝ) {D : ℝ} (hD : D ≠ 0)
    (hH0 : ∀ x, H0 (x + curvePeriod) = H0 x + D)
    (hH1 : ∀ x, H1 (x + curvePeriod) = H1 x + D)
    (B : Q.charts.Point → (EuclideanSpace ℝ (Fin m)) →L[ℝ]
      (EuclideanSpace ℝ (Fin m)) →L[ℝ] ℝ) (hB : Continuous B)
    (hei : IsEmbedding e) {K : ℝ} (hb : ∀ q, ‖B q‖ ≤ K)
    (hpos : ∀ q v, 0 ≤ B q v v) {C : ℝ}
    (hcoercive : ∀ (q : Q.charts.Point) (v : EuclideanSpace ℝ (Fin m)),
      v ∈ range (mfderiv (𝓡 ((n + 1) + 1)) (𝓡 m) e q) → ‖v‖ ^ 2 ≤ C * B q v v)
    {cap : ℝ} (hcap : 0 < cap) :
    let c0 := auxiliaryCircleSection Q q0 ∘ gamma0
    let c1 := auxiliaryCircleSection Q q1 ∘ gamma1
    ∃ lo hi : ℝ, 0 < lo ∧ lo < hi ∧
      ∀ A : M64FreeWeakPhaseAnnulus (n := (n + 1) + 1)
          e R c0 c1 H0 H1 (curvePeriod / circumference) D,
        ∀ r : ℝ, 0 < r → A.annulus.weightedEnergy B r ≤ cap → r ∈ Ioo lo hi := by
  obtain ⟨L, v0, v1, hv, h0, h1⟩ := auxiliaryCircle_exists_separating_reader P Q e T hT hne
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  have hk : curvePeriod / circumference ≠ 0 :=
    (div_pos hP P.circle.positive).ne'
  apply M64FreeWeakPhaseAnnulus.exists_strict_modulus_interval hk hD hH0 hH1
    (he.comp ((auxiliaryCircle_section_contMDiff Q q0).continuous.comp hc0))
    (he.comp ((auxiliaryCircle_section_contMDiff Q q1).continuous.comp hc1))
    L hv (fun x => h0 (gamma0 x)) (fun x => h1 (gamma1 x))
    B hB hei hb hpos hcoercive hcap

end M64
end PoincareConjecture
