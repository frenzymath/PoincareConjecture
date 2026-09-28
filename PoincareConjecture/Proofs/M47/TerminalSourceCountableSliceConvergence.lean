import PoincareConjecture.Proofs.M47.TerminalSourceCountableClosedLimit










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "V" => E →L[ℝ] E →L[ℝ] ℝ



theorem terminalSourceCountable_slice_convergence
    {tau : ℝ} (htau : 0 < tau) {U : Set E} (hU : IsOpen U)
    (f : ℕ → ℝ × E → V) (B0 : E → V) (Bminus : ℝ × E → V)
    (hzero : TendstoLocallyUniformlyOn (fun k x => f k (0, x)) B0 atTop U)
    (hminus : ∀ K, IsCompact K → K ⊆ Ioo (-(tau / 2)) 0 ×ˢ U →
      TendstoUniformlyOn (fun k => iteratedFDeriv ℝ 0 (f k))
        (iteratedFDeriv ℝ 0 Bminus) atTop K)
    {t : ℝ} (ht : t ∈ Icc (-(tau / 4)) 0) :
    TendstoLocallyUniformlyOn (fun k x => f k (t, x))
      (fun x => if t < 0 then Bminus (t, x) else B0 x) atTop U := by
  by_cases ht0 : t < 0
  · simp only [if_pos ht0]
    apply (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mpr
    intro K hKU hK
    have hprod : ({t} : Set ℝ) ×ˢ K ⊆ Ioo (-(tau / 2)) 0 ×ˢ U := by
      rintro ⟨s, x⟩ ⟨hs, hx⟩
      have hst : s = t := mem_singleton_iff.mp hs
      subst s
      exact ⟨⟨by linarith only [htau, ht.1], ht0⟩, hKU hx⟩
    have heval := (ContinuousMultilinearMap.uniformContinuous_eval_const
      (𝕜 := ℝ) (0 : Fin 0 → ℝ × E)).comp_tendstoUniformlyOn
        (hminus _ (isCompact_singleton.prod hK) hprod)
    have hvalue : TendstoUniformlyOn (fun k => f k) Bminus atTop ({t} ×ˢ K) := by
      simpa only [Function.comp_def, iteratedFDeriv_zero_apply] using heval
    simpa only [Function.comp_def] using
      (hvalue.comp (fun x : E => (t, x))).mono (fun _ hx => ⟨rfl, hx⟩)
  · have htzero : t = 0 := le_antisymm ht.2 (le_of_not_gt ht0)
    subst t
    simpa only [lt_self_iff_false, if_false] using hzero



theorem terminalSourceCountable_negative_slice_convergence
    (j : ℕ) (M : {k : ℕ // j ≤ k} → Type u)
    [∀ a, TopologicalSpace (M a)] [∀ a, ChartedSpace E (M a)]
    [∀ a, IsManifold (𝓡 3) ∞ (M a)]
    {tau R : ℝ} (htau : 0 < tau)
    (F : ∀ a, RicciFlow 3 (M a) (Icc (-tau) 0))
    (C : ∀ a, TerminalSourceChart ((F a).metric 0) R)
    (U : Opens E) (f0 : ℕ → E → V)
    (hread : ∀ a, EqOn (f0 a.val)
      (((F a).metric 0).pullbackCoefficients (C a).chart) U)
    (sigma : ℕ → ℕ) (B0 : E → V) (Bminus : ℝ × E → V)
    (hzero : ∀ K, IsCompact K → K ⊆ U →
      TendstoUniformlyOn (fun k => iteratedFDeriv ℝ 0 (f0 (sigma k)))
        (iteratedFDeriv ℝ 0 B0) atTop K)
    (hminus : ∀ K, IsCompact K → K ⊆ Ioo (-(tau / 2)) 0 ×ˢ (U : Set E) →
      TendstoUniformlyOn (fun k => iteratedFDeriv ℝ 0
        (terminalSourceCountableNegative j M F C f0 (sigma k)))
        (iteratedFDeriv ℝ 0 Bminus) atTop K)
    {t : ℝ} (ht : t ∈ Icc (-(tau / 4)) 0) :
    TendstoLocallyUniformlyOn
      (fun k x => terminalSourceCountableNegative j M F C f0 (sigma k) (t, x))
      (fun x => if t < 0 then Bminus (t, x) else B0 x) atTop U := by
  apply terminalSourceCountable_slice_convergence htau U.isOpen
    (fun k => terminalSourceCountableNegative j M F C f0 (sigma k)) B0 Bminus
    ?_ hminus ht
  have hterminal : TendstoLocallyUniformlyOn (fun k => f0 (sigma k)) B0 atTop U := by
    apply (tendstoLocallyUniformlyOn_iff_forall_isCompact U.isOpen).mpr
    intro K hKU hK
    have heval := (ContinuousMultilinearMap.uniformContinuous_eval_const
      (𝕜 := ℝ) (0 : Fin 0 → E)).comp_tendstoUniformlyOn (hzero K hK hKU)
    simpa only [Function.comp_def, iteratedFDeriv_zero_apply] using heval
  apply hterminal.congr
  exact fun k x hx =>
    (terminalSourceCountableNegative_zero j M F C U f0 hread (sigma k) hx).symm

end PoincareConjecture.M47
