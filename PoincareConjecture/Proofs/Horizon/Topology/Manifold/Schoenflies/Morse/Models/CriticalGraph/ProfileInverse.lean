import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.CriticalGraph.Profile
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function Filter
open scoped ContDiff Topology

namespace Poincare.Manifold.Schoenflies



def minimumCapHeight (z : Real) : Real :=
  if hz : 0 ≤ z ∧ z < 1 then Classical.choose (exists_unique_minimumCap_height hz.1 hz.2)
  else z

theorem minimumCapHeight_spec {z : Real} (hz : 0 ≤ z) (hz1 : z < 1) :
    minimumCapHeight z ∈ Ico (0 : Real) (1 / 2) ∧
      minimumCapSquaredRadius (minimumCapHeight z) = z := by
  rw [minimumCapHeight, dif_pos ⟨hz, hz1⟩]
  exact (Classical.choose_spec (exists_unique_minimumCap_height hz hz1)).1

theorem minimumCapHeight_eq_of_radius {z u : Real} (hz : 0 ≤ z) (hz1 : z < 1)
    (hu : u ∈ Ico (0 : Real) (1 / 2)) (heq : minimumCapSquaredRadius u = z) :
    minimumCapHeight z = u :=
  (exists_unique_minimumCap_height hz hz1).unique (minimumCapHeight_spec hz hz1) ⟨hu, heq⟩

theorem minimumCapHeight_eq_self {z : Real} (hz : z ≤ 1 / 4) : minimumCapHeight z = z := by
  by_cases hz0 : 0 ≤ z
  · exact minimumCapHeight_eq_of_radius hz0 (by linarith) ⟨hz0, by linarith⟩
      (minimumCapSquaredRadius_eq_self hz)
  · simp [minimumCapHeight, hz0]

theorem minimumCapHeight_pos {z : Real} (hz : 0 < z) (hz1 : z < 1) :
    0 < minimumCapHeight z := by
  obtain ⟨hu, heq⟩ := minimumCapHeight_spec hz.le hz1
  apply lt_of_le_of_ne hu.1
  intro hu0
  rw [← hu0, minimumCapSquaredRadius_eq_self (by norm_num : (0 : Real) ≤ 1 / 4)] at heq
  exact hz.ne heq


theorem contDiffAt_minimumCapHeight {z : Real} (hz1 : z < 1) :
    ContDiffAt Real ∞ minimumCapHeight z := by
  by_cases hzsmall : z < 1 / 4
  · apply contDiffAt_id.congr_of_eventuallyEq
    filter_upwards [gt_mem_nhds hzsmall] with y hy
    exact minimumCapHeight_eq_self hy.le
  have hz : 0 < z := by linarith
  let u := minimumCapHeight z
  have hu : u ∈ Ioo (0 : Real) (1 / 2) :=
    ⟨minimumCapHeight_pos hz hz1, (minimumCapHeight_spec hz.le hz1).1.2⟩
  have hder : deriv minimumCapSquaredRadius u ≠ 0 :=
    (deriv_minimumCapSquaredRadius_pos hu.2).ne'
  let L : Real ≃L[Real] Real :=
    (LinearEquiv.smulOfNeZero Real Real (deriv minimumCapSquaredRadius u) hder).toContinuousLinearEquiv
  have hd : HasFDerivAt minimumCapSquaredRadius L.toContinuousLinearMap u := by
    convert! (contDiff_minimumCapSquaredRadius.differentiable (by simp) u).hasFDerivAt using 1
    ext
    simp [L]
  have hf := contDiff_minimumCapSquaredRadius.contDiffAt (x := u)
  let Q := hf.toOpenPartialHomeomorph minimumCapSquaredRadius hd (by simp)
  have huQ : u ∈ Q.source := hf.mem_toOpenPartialHomeomorph_source hd (by simp)
  have hQu : Q u = z := (minimumCapHeight_spec hz.le hz1).2
  have hzQ : z ∈ Q.target := hQu ▸ Q.map_source huQ
  have hQi : ContDiffAt Real ∞ Q.symm z := by
    have hi := hf.to_localInverse hd (by simp)
    change ContDiffAt Real ∞ Q.symm (minimumCapSquaredRadius u) at hi
    simpa only [show minimumCapSquaredRadius u = z from hQu] using hi
  have hQizu : Q.symm z = u := by rw [← hQu, Q.left_inv huQ]
  have hQipos : ∀ᶠ y in 𝓝 z, Q.symm y ∈ Ioo (0 : Real) (1 / 2) :=
    hQi.continuousAt.eventually (isOpen_Ioo.mem_nhds (hQizu ▸ hu))
  apply hQi.congr_of_eventuallyEq
  filter_upwards [hQipos, Q.open_target.mem_nhds hzQ, lt_mem_nhds hz, gt_mem_nhds hz1]
    with y hy hyQ hy0 hy1
  exact minimumCapHeight_eq_of_radius hy0.le hy1 ⟨hy.1.le, hy.2⟩ (Q.right_inv hyQ)

theorem contDiffOn_minimumCapHeight : ContDiffOn Real ∞ minimumCapHeight (Iio 1) :=
  fun _ hz => (contDiffAt_minimumCapHeight hz).contDiffWithinAt

end Poincare.Manifold.Schoenflies
