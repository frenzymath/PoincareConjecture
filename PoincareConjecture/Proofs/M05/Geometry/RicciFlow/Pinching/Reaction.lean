
import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Pinching.Algebra








namespace Poincare







theorem pinchingReactionBarrier
    {lam mu nu : ℝ} {S X : ℝ → ℝ} {t dS dX : ℝ}
    (hmu : mu ≤ lam) (hnu : nu ≤ mu)
    (hXval : X t = -nu) (hSval : S t = lam + mu + nu)
    (hS : HasDerivAt S dS t) (hX : HasDerivAt X dX t)
    (hdS : dS = X t ^ 2 + (-mu) ^ 2 + lam ^ 2 + X t * (-mu) -
      lam * (X t + (-mu)))
    (hdX : dX = -X t ^ 2 + (-mu) * lam)
    (hXpos : 0 < X t) :
    X t ≤ deriv (fun s => S s / X s - Real.log (X s)) t := by
  have hnu0 : nu ≤ 0 := by
    have h : 0 ≤ -nu := by simpa [hXval] using hXpos.le
    exact neg_nonneg.mp h
  have hreaction := pinchingReactionInequality
    (lam := lam) (X := -nu) (Y := -mu)
    (neg_nonneg.mpr hnu0) (neg_le_neg hnu) (by simpa using hmu)
  have hdS' : dS = (-nu) ^ 2 + (-mu) ^ 2 + lam ^ 2 +
      (-nu) * (-mu) - lam * ((-nu) + (-mu)) := by
    simpa [hXval] using hdS
  have hdX' : dX = -(-nu) ^ 2 + (-mu) * lam := by
    simpa [hXval] using hdX
  have hineq : X t ^ 3 ≤ X t * dS - (S t + X t) * dX := by
    calc
      X t ^ 3 = (-nu) ^ 3 := by rw [hXval]
      _ ≤ (-nu) * ((-nu) ^ 2 + (-mu) ^ 2 + lam ^ 2 +
          (-nu) * (-mu) - lam * ((-nu) + (-mu))) -
          (lam - (-nu) - (-mu) + (-nu)) *
            (-(-nu) ^ 2 + (-mu) * lam) := hreaction
      _ = X t * dS - (S t + X t) * dX := by
        rw [hXval, hSval, hdS', hdX']
        ring
  exact derivPinchingLogQuantityGe hS hX hXpos hineq

end Poincare
