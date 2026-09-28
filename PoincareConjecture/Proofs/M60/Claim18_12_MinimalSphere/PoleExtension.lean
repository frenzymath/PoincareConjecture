import PoincareConjecture.Proofs.M60.Mathlib.ChartedDenseComplement
import PoincareConjecture.Proofs.M60.Mathlib.ScalarGradientSquare
import PoincareConjecture.Proofs.M60.Claim18_12_MinimalSphere.RoundMetric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

theorem m60RoundSphere_extend_regular_inequality
    (D : LeviCivitaData m60RoundSphereMetric) {q k : UnitTwoSphere → ℝ}
    (hq : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ q) (hk : Continuous k)
    (hreg : ∀ p, p ≠ m60SpherePole → 0 < q p →
      M04.scalarGradientSq m60RoundSphereMetric q p / q p + 2 * q p -
        2 * q p * k p ≤ D.laplacian q p) :
    ∀ p, 0 < q p →
      M04.scalarGradientSq m60RoundSphereMetric q p / q p + 2 * q p -
        2 * q p * k p ≤ D.laplacian q p := by
  intro p hp
  by_cases heq : p = m60SpherePole
  · subst p
    have hd : Dense ({m60SpherePole}ᶜ : Set UnitTwoSphere) :=
      M60.dense_compl_singleton_of_charted (H := LoopPlane) m60SpherePole
    let : NeBot (𝓝[≠] m60SpherePole) :=
      mem_closure_iff_nhdsWithin_neBot.mp (hd m60SpherePole)
    have hleft : ContinuousAt (fun p =>
        M04.scalarGradientSq m60RoundSphereMetric q p / q p + 2 * q p -
          2 * q p * k p) m60SpherePole :=
      (((M60.contMDiff_scalarGradientSq D hq).continuous.continuousAt.div
        hq.continuous.continuousAt hp.ne').add
        (continuousAt_const.mul hq.continuous.continuousAt)).sub
        ((continuousAt_const.mul hq.continuous.continuousAt).mul hk.continuousAt)
    have hpos : ∀ᶠ y in 𝓝 m60SpherePole, 0 < q y :=
      hq.continuous.continuousAt.eventually (lt_mem_nhds hp)
    apply le_of_tendsto_of_tendsto (b := 𝓝[≠] m60SpherePole)
      (hleft.tendsto.mono_left nhdsWithin_le_nhds)
      ((D.continuous_laplacian hq).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    filter_upwards [self_mem_nhdsWithin, hpos.filter_mono nhdsWithin_le_nhds] with y hy hqy
    exact hreg y hy hqy
  · exact hreg p heq hp

end PoincareConjecture
