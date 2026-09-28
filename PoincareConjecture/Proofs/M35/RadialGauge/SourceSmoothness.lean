import PoincareConjecture.Proofs.M35.RadialGauge.RadialSymmetry
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Calculus










set_option autoImplicit false

open scoped ContDiff

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)



theorem contDiff_squared_dual_norm
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {p : X → V →L[ℝ] ℝ} (hp : ContDiff ℝ ∞ p) :
    ContDiff ℝ ∞ (fun x => ‖p x‖ ^ 2) := by
  simp_rw [(EuclideanSpace.basisFun (Fin n) ℝ).norm_dual]
  apply ContDiff.sum
  intro i _
  exact (hp.clm_apply contDiff_const).pow 2



theorem gaugeSource_contDiff {b : V → V} {G : V → ℝ → ℝ} {u : V → ℝ}
    (hb : ContDiff ℝ ∞ b)
    (hG : ContDiff ℝ ∞ (fun p : V × ℝ => G p.1 p.2))
    (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (gaugeSource b G u) := by
  have hdu := (contDiff_infty_iff_fderiv.mp hu).2
  exact ((hdu.clm_apply hb).add (contDiff_squared_dual_norm hdu)).add
    (hG.comp (contDiff_id.prodMk hu))




theorem parametrizedGaugeSource_contDiff
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {b : X → V} {G : X → ℝ → ℝ} {u : X → ℝ} {p : X → V →L[ℝ] ℝ}
    (hb : ContDiff ℝ ∞ b)
    (hG : ContDiff ℝ ∞ (fun q : X × ℝ => G q.1 q.2))
    (hu : ContDiff ℝ ∞ u) (hp : ContDiff ℝ ∞ p) :
    ContDiff ℝ ∞ (fun x => semilinearSource (b x) (G x) (u x) (p x)) := by
  exact ((hp.clm_apply hb).add (contDiff_squared_dual_norm hp)).add
    (hG.comp (contDiff_id.prodMk hu))

end PoincareConjecture.M35.RadialGauge
