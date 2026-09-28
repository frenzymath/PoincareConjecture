import PoincareConjecture.Proofs.M65.Sec19_5_GoodTimes.FamilyCellFillingLimit
import Mathlib.Analysis.SpecificLimits.Basic










set_option autoImplicit false

open Set Filter
open scoped Topology ContDiff Manifold Bundle

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ} {F : RicciFlow 3 M (Icc a b)}
  {Gamma : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))} {zeta : ℝ}

set_option maxHeartbeats 1200000 in






theorem m65FamilyCell_exists_comparison_cutoff (hM64 : M64ComparisonTheory.{u})
    (compact : IsCompact (univ : Set M)) (V : M64ThreeDimensionalFlowConclusion F)
    (C : M63FamilyConclusion V.flow.geometry Gamma zeta)
    (comparison : M65ImmersedFillingAreaComparison F) (z : LoopTwoSphere)
    {r s ell u v error : ℝ} (hrs : r ≤ s) (hsub : Icc r s ⊆ Ioo a b)
    (hell : 0 < ell) (B : ℕ → ℝ) (hB : ∀ i, 0 ≤ B i)
    (huv : u ≤ v) (hinside : Icc u v ⊆ Ioo r s) (herror : 0 < error) :
    ∃ cutoff : ℝ, 0 < cutoff ∧ ∀ circumference (h : 0 < circumference),
      circumference < 1 → circumference < cutoff →
      ell ≤ m62Length (V.flow.geometry.product circumference h).flow
        ((C.solutions circumference h).curve z) r →
      (∀ t ∈ Icc r s, ∀ i x,
        m63CurvatureJetSquared (V.flow.geometry.product circumference h).flow
          ((C.solutions circumference h).curve z) i t x ≤ B i) →
      fillingArea (F.metric v) ((C.solutions circumference h).projected
          ⟨v, Ioo_subset_Icc_self (hsub (Ioo_subset_Icc_self (hinside ⟨huv, le_rfl⟩)))⟩ z) ≤
        m65RestartedAreaProfile F u
          (fillingArea (F.metric u) ((C.solutions circumference h).projected
            ⟨u, Ioo_subset_Icc_self (hsub (Ioo_subset_Icc_self (hinside ⟨le_rfl, huv⟩)))⟩ z))
          v + error := by
  classical
  by_contra! hfail
  have hseq (k : ℕ) := hfail (1 / ((k : ℝ) + 1)) (by positivity)
  choose circumference h hlt hsmall hlength hjets hbad using hseq
  have hzero : Tendsto circumference atTop (𝓝 0) :=
    squeeze_zero (fun k => (h k).le) (fun k => (hsmall k).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨select, _hselect, L, hequation, harea⟩ :=
    m65FamilyCell_exists_filled_limit hM64 compact V C circumference h hlt hzero z
      hrs hsub hell hlength B hB (fun k t x ht i => hjets k t ht i x)
  have hu : u ∈ Ioo r s := hinside ⟨le_rfl, huv⟩
  have hv : v ∈ Ioo r s := hinside ⟨huv, le_rfl⟩
  have hcomp := comparison (Ioo r s) isOpen_Ioo
    (fun _ ht => hsub (Ioo_subset_Icc_self ht)) L hequation u v huv hinside
  have hprofile : Continuous (fun A : ℝ => m65RestartedAreaProfile F u A v) := by
    unfold m65RestartedAreaProfile
    fun_prop
  have hleft := ((hprofile.tendsto _).comp (harea ⟨u, hu⟩)).add_const error
  have hright := harea ⟨v, hv⟩
  have hcontr := le_of_tendsto_of_tendsto hleft hright
    (Eventually.of_forall (fun k => (hbad (select k)).le))
  linarith

end PoincareConjecture
