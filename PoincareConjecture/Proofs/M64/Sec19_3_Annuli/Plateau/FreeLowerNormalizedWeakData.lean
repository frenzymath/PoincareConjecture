import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeLowerHolder
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.ObservedRepresentativeWeakData
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.SourceCoordinateEnergy
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusNormalizedBoundaryDomain

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric MeasureTheory
open scoped Topology Manifold ContDiff
open Poincare.Analysis.Sobolev.Weak

namespace PoincareConjecture.M64FreeWeakPhaseAnnulus

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)}
  {Robs : EuclideanSpace ℝ (Fin m) →L[ℝ] LoopPlane} {c0 c1 : ℝ → M}
  {H0 H1 : ℝ ≃o ℝ} {k degree : ℝ}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain

theorem lower_normalized_weak_data
    (A : M64FreeWeakPhaseAnnulus (n := n) e Robs c0 c1 H0 H1 k degree)
    (he : ContMDiff (𝓡 n) (𝓡 m) ∞ e)
    (hA : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.annulus.map S)
    (hc0 : Continuous (e ∘ c0)) (hc1 : Continuous (e ∘ c1))
    (hH0 : ∀ y, H0 (y + curvePeriod) = H0 y + degree)
    (hH1 : ∀ y, H1 (y + curvePeriod) = H1 y + degree)
    {x0 rho K beta s : ℝ} (hrho : 0 < rho) (hs : 0 < s)
    (hsub : closedBall (annulusPoint x0 0) (2 * rho) ⊆ m64AnnulusLowerDomain)
    (hK : 0 ≤ K) (hbeta : 0 < beta)
    (henergy : ∀ b ∈ closedBall (annulusPoint x0 0) rho, ∀ r ∈ Ioc (0 : ℝ) rho,
      (∫ p in closedBall b r ∩ S, ∑ i : Fin 2, ‖A.annulus.column i p‖ ^ 2) ≤ K * r ^ beta) :
    let Phi := m64SourceAffine (annulusPoint x0 0) s hs.ne'
    let V := fun i p => m64SourceScaleFactor s i • A.annulus.lowerReflectedColumn i (Phi p)
    ∃ tau : ℝ, 0 < tau ∧ ∃ H Lambda : ℝ, 0 ≤ H ∧ 0 ≤ Lambda ∧ ∃ U : LoopPlane → E,
      MapsTo Phi (ball (0 : LoopPlane) (2 * tau) ∩ {z | 0 < z 1}) S ∧
      MemLp U 2 (volume.restrict (ball (0 : LoopPlane) (2 * tau))) ∧
      (∀ i, MemLp (V i) 2 (volume.restrict (ball (0 : LoopPlane) (2 * tau)))) ∧
      (∀ i j, HasWeakPartialDeriv i (fun z => V i z j) (fun z => U z j)
        (ball (0 : LoopPlane) (2 * tau))) ∧
      ContinuousOn U (closedBall (0 : LoopPlane) (2 * tau)) ∧
      ContDiffOn ℝ 2 U (ball (0 : LoopPlane) (2 * tau) ∩ {z | 0 < z 1}) ∧
      EqOn U (e ∘ (A.annulus.map ∘ Phi))
        (ball (0 : LoopPlane) (2 * tau) ∩ {z | 0 < z 1}) ∧
      (∀ z ∈ closedBall (0 : LoopPlane) (2 * tau), z 1 = 0 →
        U z = e (c0 (A.label0 (x0 + s * z 0)))) ∧
      (∀ x ∈ closedBall (0 : LoopPlane) tau, ∀ z ∈ closedBall (0 : LoopPlane) tau,
        ‖U z - U x‖ ≤ H * dist z x ^ (beta / 2)) ∧
      ∀ x ∈ closedBall (0 : LoopPlane) (tau / 2),
        ∀ r : ℝ, 0 < r → r ≤ tau / 2 →
        (∫ z in closedBall x r, ∑ i : Fin 2, ‖V i z‖ ^ 2) ≤ Lambda * r ^ beta := by
  let a := annulusPoint x0 0
  let Phi := m64SourceAffine a s hs.ne'
  let V := fun i p => m64SourceScaleFactor s i • A.annulus.lowerReflectedColumn i (Phi p)
  let kappa := ‖(m64SourceScale s hs.ne').toContinuousLinearMap‖ + 1
  have hk : 0 < kappa := by dsimp only [kappa]; positivity
  have hD : ‖(m64SourceScale s hs.ne').toContinuousLinearMap‖ ≤ kappa :=
    le_add_of_nonneg_right zero_le_one
  let tau := rho / (16 * kappa)
  have htau : 0 < tau := div_pos hrho (by positivity)
  have htauEq : (16 * kappa) * tau = rho := mul_div_cancel₀ rho (by positivity)
  have hsmall : kappa * (2 * (2 * tau)) < rho / 2 := by nlinarith only [htauEq, hrho]
  have hm : MapsTo Phi (closedBall (0 : LoopPlane) (2 * (2 * tau))) (ball a (rho / 2)) :=
    m64SourceAffine_mapsTo_ball a s hs.ne' hk.le hD hsmall
  have hhalf : ball a (rho / 2) ⊆ m64AnnulusLowerDomain :=
    (ball_subset_closedBall.trans (closedBall_subset_closedBall
      (by linarith only [hrho] : rho / 2 ≤ 2 * rho))).trans hsub
  obtain ⟨H, hH, U0, hU0, hUae, hholder⟩ :=
    A.annulus.lower_holder_representative hrho hsub hK hbeta henergy
  obtain ⟨hpoint, htrace⟩ := A.lower_representative_trace (he.of_le (by simp))
    (hA.of_le (by simp)) hc0 hc1 hH0 hH1 isOpen_ball hhalf
    (hU0.mono ball_subset_closedBall) hUae
  obtain ⟨-, hV, hw⟩ := A.annulus.lower_representative_weak_data isOpen_ball hhalf hUae
  have hid : ∀ y : E, ‖fderiv ℝ (id : E → E) y‖ ≤ (1 : ℝ) := fun y => by
    simpa only [fderiv_id] using
      (ContinuousLinearMap.norm_id_le : ‖ContinuousLinearMap.id ℝ E‖ ≤ 1)
  have hweakData := m64SourceCoordinate_weak_data a s hs.ne'
    (by positivity : 0 < 2 * tau) hk.le hD hsmall hU0 hV hw
    (contDiff_id : ContDiff ℝ 1 (id : E → E)) zero_lt_one hid
  have hdata :
      MemLp (U0 ∘ Phi) 2 (volume.restrict (ball (0 : LoopPlane) (2 * (2 * tau)))) ∧
      (∀ i, MemLp (V i) 2 (volume.restrict (ball (0 : LoopPlane) (2 * (2 * tau))))) ∧
      (∀ i j, HasWeakPartialDeriv i (fun z => V i z j) (fun z => (U0 ∘ Phi) z j)
        (ball (0 : LoopPlane) (2 * tau))) ∧
      ContinuousOn (U0 ∘ Phi) (closedBall (0 : LoopPlane) (2 * (2 * tau))) := by
    simpa only [Function.comp_def, id_eq, fderiv_id, ContinuousLinearMap.id_apply] using hweakData
  have hrad : 2 * tau ≤ 2 * (2 * tau) := by linarith only [htau]
  have hm2 (z : LoopPlane) (hz : z ∈ closedBall 0 (2 * tau)) : Phi z ∈ ball a (rho / 2) :=
    hm (closedBall_subset_closedBall hrad hz)
  have hinto : MapsTo Phi (ball (0 : LoopPlane) (2 * tau) ∩ {z | 0 < z 1}) S :=
    fun z hz => m64AnnulusSourceAffine_interior x0 hs
      (hhalf (hm2 z (ball_subset_closedBall hz.1))) hz.2
  have hobs : EqOn (U0 ∘ Phi) (e ∘ (A.annulus.map ∘ Phi))
      (ball (0 : LoopPlane) (2 * tau) ∩ {z | 0 < z 1}) :=
    fun z hz => hpoint ⟨hm2 z (ball_subset_closedBall hz.1), hinto hz⟩
  have hsource : ContMDiff (𝓡 2) (𝓡 2) ∞ Phi :=
    (m64SourceAffine_contDiff a s hs.ne').contMDiff
  have hsm : ContDiffOn ℝ 2 (U0 ∘ Phi)
      (ball (0 : LoopPlane) (2 * tau) ∩ {z | 0 < z 1}) := by
    have hobsSm := he.comp_contMDiffOn (hA.comp hsource.contMDiffOn hinto)
    exact (hobsSm.contDiffOn.of_le (WithTop.coe_le_coe.mpr le_top)).congr (fun z hz => hobs hz)
  have hcol (i : Fin 2) : MemLp (V i) 2
      (volume.restrict (ball (0 : LoopPlane) (2 * tau))) :=
    (hdata.2.1 i).mono_measure (Measure.restrict_mono_set volume (ball_subset_ball hrad))
  have henergy' := m64SourceCoordinate_energy_growth U0 A.annulus.lowerReflectedColumn
    (id : E → E) a s hs.ne' (by positivity : 0 < 2 * tau) hk zero_le_one hD
    (by nlinarith only [htauEq, hrho] : kappa * (2 * tau) ≤ rho) hsub
    A.annulus.lower_reflected_memLp.2 hid
    (A.annulus.lower_reflected_energy_closed_growth hsub henergy)
    (by simpa only [fderiv_id, ContinuousLinearMap.id_apply] using hcol)
  refine ⟨tau, htau, H * kappa ^ (beta / 2),
    kappa ^ 2 * (4 * K) * kappa ^ beta, by positivity, by positivity,
    U0 ∘ Phi, hinto, ?_, hcol, hdata.2.2.1, ?_, hsm, hobs, ?_, ?_, ?_⟩
  · exact hdata.1.mono_measure (Measure.restrict_mono_set volume (ball_subset_ball hrad))
  · exact hdata.2.2.2.mono (closedBall_subset_closedBall hrad)
  · intro z hz hz0
    change U0 (Phi z) = _
    have hface := m64AnnulusSourceAffine_face x0 s hs.ne' hz0
    have hmz := hm2 z hz
    change Phi z = annulusPoint (x0 + s * z 0) 0 at hface
    rw [hface] at hmz ⊢
    exact htrace _ hmz
  · intro x hx z hz
    have hh := m64SourceCoordinate_holder a s hs.ne' hk.le hH (half_pos hbeta).le hD
      (by nlinarith only [htauEq, hrho] : kappa * tau ≤ rho / 2)
      (LipschitzWith.id : LipschitzWith 1 (id : E → E)) hholder z hz x hx
    simpa only [id_eq, NNReal.coe_one, one_mul, dist_eq_norm, Function.comp_apply] using hh
  · simpa only [one_mul, fderiv_id, ContinuousLinearMap.id_apply,
      show 2 * tau / 4 = tau / 2 from by ring] using henergy'

end PoincareConjecture.M64FreeWeakPhaseAnnulus
