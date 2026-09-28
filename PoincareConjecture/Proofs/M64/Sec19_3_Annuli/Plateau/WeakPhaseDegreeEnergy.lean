import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakVerticalSeparation
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.CirclePhaseEnergy

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain

theorem M64ObservedWeakAnnulus.weightedEnergy_ge_phase_lift
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q)
    (hei : IsEmbedding e) {K : ℝ} (hK : ∀ q, ‖Q q‖ ≤ K)
    (hpos : ∀ q v, 0 ≤ Q q v v) {C : ℝ}
    (L : LoopPlane → ℝ) (hL : ContDiff ℝ 1 L) {d : ℝ}
    (hshift : ∀ x s, L (annulusPoint (x + curvePeriod) s) =
      L (annulusPoint x s) + d)
    (hder : ∀ᵐ p ∂volume.restrict S,
      (fderiv ℝ L p (EuclideanSpace.single (0 : Fin 2) 1)) ^ 2 ≤
        C * Q (A.map p) (A.column 0 p) (A.column 0 p))
    {r : ℝ} (hr : 0 < r) :
    r * d ^ 2 / (2 * curvePeriod * (max C 1)) ≤ A.weightedEnergy Q r := by
  let D : LoopPlane → ℝ := fun p =>
    (fderiv ℝ L p (EuclideanSpace.single (0 : Fin 2) 1)) ^ 2
  let C' := max C 1
  have hC' : 0 < C' := by dsimp [C']; exact lt_max_of_lt_right zero_lt_one
  have hCnonneg : 0 ≤ C' := hC'.le
  have hD : Continuous D :=
    ((hL.continuous_fderiv (by simp)).clm_apply continuous_const).pow 2
  have hDint : IntegrableOn D S volume :=
    hD.continuousOn.integrableOn_compact m64AnnulusDomain_isCompact |>.mono_set interior_subset
  have hqint := A.column_energy_integrable Q hQ hei hK 0
  have hder' : ∀ᵐ p ∂volume.restrict S, D p ≤ C' *
      Q (A.map p) (A.column 0 p) (A.column 0 p) := by
    filter_upwards [hder] with p hp
    exact hp.trans (mul_le_mul_of_nonneg_right (le_max_left C 1) (hpos _ _))
  have hDle : (∫ p in S, D p) ≤ C' *
      ∫ p in S, Q (A.map p) (A.column 0 p) (A.column 0 p) := by
    have hh := integral_mono_ae hDint (hqint.const_mul C') hder'
    rw [integral_const_mul] at hh
    exact hh
  have hphase := m64Annulus_phase_energy hL hshift
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  have hphase' : d ^ 2 ≤ curvePeriod * (C' *
      ∫ p in S, Q (A.map p) (A.column 0 p) (A.column 0 p)) :=
    hphase.trans (mul_le_mul_of_nonneg_left hDle (by unfold curvePeriod; positivity))
  rw [A.weightedEnergy_eq_column_integrals Q hQ hei hK r]
  have hq0 : 0 ≤ ∫ p in S, Q (A.map p) (A.column 0 p) (A.column 0 p) :=
    integral_nonneg fun p => hpos _ _
  have hq1 : 0 ≤ ∫ p in S, Q (A.map p) (A.column 1 p) (A.column 1 p) :=
    integral_nonneg fun p => hpos _ _
  have hmain : r * d ^ 2 / (2 * curvePeriod * C') ≤
      (r / 2) * ∫ p in S, Q (A.map p) (A.column 0 p) (A.column 0 p) := by
    apply (div_le_iff₀ (mul_pos (mul_pos (by norm_num) hP) hC')).mpr
    have hh := mul_le_mul_of_nonneg_left hphase' (by positivity : 0 ≤ r)
    field_simp [hC'.ne', hr.ne'] at hh ⊢
    nlinarith
  exact hmain.trans (le_add_of_nonneg_right
    (mul_nonneg (by positivity) hq1))

end PoincareConjecture
