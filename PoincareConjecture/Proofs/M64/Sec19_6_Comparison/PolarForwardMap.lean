import PoincareConjecture.Proofs.M64.Sec19_6_Comparison.PolarAnnulusMap
import PoincareConjecture.Proofs.M58.Cor18_28_PolarDerivatives
import Mathlib.Analysis.Calculus.FDeriv.WithLp

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold

namespace PoincareConjecture

open Proofs.M58

noncomputable def m64PolarForwardMap (p : LoopPlane) : LoopPlane :=
  ((1 / 2 : ℝ) * (p 1 + 1)) • angularPoint (p 0)

theorem m64PolarForwardMap_hasFDerivAt (p : LoopPlane) :
    HasFDerivAt (𝕜 := ℝ) m64PolarForwardMap
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0).smulRight
          (((1 / 2 : ℝ) * (p 1 + 1)) • angularVector (p 0)) +
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1).smulRight
          ((1 / 2 : ℝ) • angularPoint (p 0))) p := by
  have h0 := PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 p (0 : Fin 2)
  have h1 := PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 p (1 : Fin 2)
  have hs := (h1.add_const 1).const_mul (1 / 2 : ℝ)
  have ha := (hasDerivAt_angularPoint (p 0)).hasFDerivAt.comp p h0
  convert! hs.smul ha using 1
  ext w i
  change w 0 * (((1 / 2 : ℝ) * (p 1 + 1)) * angularVector (p 0) i) +
      w 1 * ((1 / 2 : ℝ) * angularPoint (p 0) i) =
    ((1 / 2 : ℝ) * (p 1 + 1)) * (w 0 * angularVector (p 0) i) +
      ((1 / 2 : ℝ) * w 1) * angularPoint (p 0) i
  ring

theorem m64PolarAnnulusMap_comp_forward
    {Y : Type*} {f : LoopPlane → Y}
    (hperiodic : ∀ x s : ℝ,
      f (annulusPoint (x + curvePeriod) s) = f (annulusPoint x s))
    {p : LoopPlane} (hp : -1 < p 1) :
    m64PolarAnnulusMap f (m64PolarForwardMap p) = f p := by
  have hr : 0 < (1 / 2 : ℝ) * (p 1 + 1) := by linarith
  have h := m64PolarAnnulusMap_polar hperiodic hr (p 0)
  have harg : 2 * ((1 / 2 : ℝ) * (p 1 + 1)) - 1 = p 1 := by ring
  rw [harg] at h
  have hpoint : annulusPoint (p 0) (p 1) = p := by ext i; fin_cases i <;> rfl
  simpa only [m64PolarForwardMap, hpoint] using h

theorem m64PolarAnnulusMap_comp_forward_eventually
    {Y : Type*} {f : LoopPlane → Y}
    (hperiodic : ∀ x s : ℝ,
      f (annulusPoint (x + curvePeriod) s) = f (annulusPoint x s))
    {p : LoopPlane} (hp : -1 < p 1) :
    (m64PolarAnnulusMap f ∘ m64PolarForwardMap) =ᶠ[𝓝 p] f := by
  have hopen : IsOpen {q : LoopPlane | -1 < q 1} :=
    isOpen_lt continuous_const (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1)
  filter_upwards [hopen.mem_nhds hp] with q hq
  exact m64PolarAnnulusMap_comp_forward hperiodic hq

end PoincareConjecture
