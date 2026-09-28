import PoincareConjecture.Proofs.M10.SquarePathEnergyBound
import PoincareConjecture.Proofs.M10.PathEnergyDistance









set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}


theorem terminalSquareEnergy_nonneg (G : LExponentialGeometry F T τmax p)
    (Z : TangentSpace (𝓡 n) p) (s : ℝ) : 0 ≤ terminalSquareEnergy G Z s := by
  by_cases hv : curveVelocity (n := n) (G.squareFamily Z) s = 0
  · simp [terminalSquareEnergy, hv]
  · exact ((F.metric T).pos _ _ hv).le


theorem edist_squareFamily_le_of_energy
    (G : LExponentialGeometry F T τmax p) (Z : TangentSpace (𝓡 n) p)
    {τ K : ℝ} (hτ : 0 < τ) (hmax : τ < τmax)
    (henergy : (∫ s in 0..Real.sqrt τ, terminalSquareEnergy G Z s) ≤ K)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ Real.sqrt τ) :
    (F.metric T).edist (G.squareFamily Z a) (G.squareFamily Z b) ≤
      ENNReal.ofReal (Real.sqrt (K * (b - a))) := by
  have hU : IsOpen {s : ℝ | (Z, s) ∈ G.squareDomain} :=
    G.square_open.preimage (continuous_const.prodMk continuous_id)
  have hI : Icc a b ⊆ {s : ℝ | (Z, s) ∈ G.squareDomain} := by
    intro s hs
    apply G.square_contains
    exact ⟨mem_univ _, ha.trans hs.1,
      (hs.2.trans hb).trans_lt (Real.sqrt_lt_sqrt hτ.le hmax)⟩
  have hd := edist_le_sqrt_curve_energy (F.metric T) hU
    ((squareFamily_contMDiffOn G Z).of_le (by decide)) hab hI
  change (F.metric T).edist _ _ ≤ ENNReal.ofReal
    (Real.sqrt ((b - a) * ∫ s in a..b, terminalSquareEnergy G Z s)) at hd
  apply hd.trans
  apply ENNReal.ofReal_le_ofReal
  apply Real.sqrt_le_sqrt
  have hint := intervalIntegral.integral_mono_interval (μ := volume) ha hab hb
    (Eventually.of_forall (terminalSquareEnergy_nonneg G Z))
    ((terminalSquareEnergy_continuousOn G Z hτ hmax).intervalIntegrable_of_Icc
      (Real.sqrt_nonneg τ))
  simpa only [mul_comm K] using
    mul_le_mul_of_nonneg_left (hint.trans henergy) (sub_nonneg.mpr hab)

end PoincareConjecture.M10
