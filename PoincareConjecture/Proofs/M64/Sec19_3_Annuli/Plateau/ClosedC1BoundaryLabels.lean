import PoincareConjecture.Proofs.M64.Mathlib.ImmersedCurveWithinComposition
import PoincareConjecture.Proofs.M64.Mathlib.MonotonePeriodicLipschitz
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryModulus
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerAnnularConvergence









noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin m)




theorem m64ObservedCurve_deriv_ne_zero
    {e : M → E} (he : ContMDiff (𝓡 n) (𝓡 m) ∞ e)
    (hread : M60.SUChartReadable (n := n) e) {c : ℝ → M}
    (hc : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 c)
    (hregular : ∀ t, curveVelocity (n := n) c t ≠ 0) (t : ℝ) :
    deriv (e ∘ c) t ≠ 0 := by
  have hchain := mfderiv_comp_apply t ((he (c t)).mdifferentiableAt (by simp))
    ((hc t).mdifferentiableAt (by norm_num)) (1 : ℝ)
  rw [mfderiv_eq_fderiv] at hchain
  change fderiv ℝ (e ∘ c) t 1 =
    mfderiv (𝓡 n) (𝓡 m) e (c t) (curveVelocity c t) at hchain
  rw [fderiv_apply_one_eq_deriv] at hchain
  intro hz
  apply hregular t
  apply M60.suChartReadable_differential_injective he hread (c t)
  rw [← hchain, hz, map_zero]




theorem m64ClosedC1Trace_exists_degreeOneLift
    {e : M → E} (he : ContMDiff (𝓡 n) (𝓡 m) ∞ e)
    (hread : M60.SUChartReadable (n := n) e) {c : ℝ → M}
    (hc : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 c)
    (hregular : ∀ t, curveVelocity (n := n) c t ≠ 0)
    {phi : ℝ → ℝ} (hphi : Continuous phi) (hm : Monotone phi)
    (hperiod : ∀ x, phi (x + curvePeriod) = phi x + curvePeriod)
    {U : LoopPlane → M} (hU : ContMDiffOn (𝓡 2) (𝓡 n) 1 U m64AnnulusDomain)
    {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1)
    (htrace : ∀ x ∈ Icc (0 : ℝ) curvePeriod, U (annulusPoint x y) = c (phi x)) :
    ∃ sigma : M64PeriodicDegreeOneLift, sigma.map = phi := by
  have he1 : ContMDiff (𝓡 n) (𝓡 m) 1 e := he.of_le (by simp)
  have hobs : ContDiff ℝ 1 (e ∘ c) := (he1.comp hc).contDiff
  have hUobs : ContDiffOn ℝ 1 (e ∘ U) m64AnnulusDomain :=
    (he1.comp_contMDiffOn hU).contDiffOn
  have haxis : ContDiff ℝ 1 (fun x : ℝ => annulusPoint x y) := by
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · simpa [annulusPoint] using! (contDiff_id : ContDiff ℝ 1 (id : ℝ → ℝ))
    · simpa [annulusPoint] using (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => y))
  have hmaps : MapsTo (fun x : ℝ => annulusPoint x y) (Icc (0 : ℝ) curvePeriod)
      m64AnnulusDomain := fun _ hx => ⟨hx.1, hx.2, hy⟩
  have hcomp : ContDiffOn ℝ 1 ((e ∘ c) ∘ phi) (Icc (0 : ℝ) curvePeriod) :=
    (hUobs.comp haxis.contDiffOn hmaps).congr
      (fun x hx => congrArg e (htrace x hx).symm)
  obtain ⟨K, hK⟩ := m64Label_lipschitzOn_of_regular_trace hphi.continuousOn hobs
    (m64ObservedCurve_deriv_ne_zero he hread hc hregular) hcomp
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  have hglobal := m64Monotone_lipschitz_of_periodic_interval hP hm hperiod hK
  refine ⟨⟨phi, hm, hperiod, K, K.coe_nonneg, ?_⟩, rfl⟩
  intro x z
  simpa only [Real.dist_eq] using hglobal.dist_le_mul x z

end PoincareConjecture
