import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2TraceSpeedGradient
import PoincareConjecture.Proofs.M62.Lemma0_4_Periodicity
import PoincareConjecture.Proofs.M62.Lemma19_6_InteriorRegularity
import PoincareConjecture.Proofs.M08.SecondVariationCoordinates
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Topology.CompactOpen

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

theorem exists_closed_curveSpeed_gradient_path [T2Space M]
    (F : RicciFlow n M (Icc a b)) (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) {K R J v0 : ℝ}
    (hK : 0 ≤ K) (hR : 0 ≤ R) (hJ : 0 ≤ J) (hv0 : 0 < v0)
    (hBounds : CurveEvolutionAmbientBounds F K K K)
    (hInitial : ∀ y, curveSpeed F c a y = v0)
    (hCurv : ∀ t ∈ Ioo a b, ∀ x, m62CurvatureSquared F c t x ≤ R)
    (hJet : ∀ t ∈ Ioo a b, ∀ x,
      (F.metric t).tangentNorm (c x t) (m63CurvatureJet F c 1 t x) ≤
        J / Real.sqrt (t - a))
    {s : ℝ} (_has : a ≤ s) (hsb : s < b) :
    ∃ G : C(Icc a s, C(AddCircle curvePeriod, ℝ)),
      ∀ (t : Icc a s) (x : ℝ),
        G t (x : AddCircle curvePeriod) =
          deriv (curveSpeed F c (t : ℝ)) x := by
  classical
  let v : ℝ × ℝ → ℝ := fun z => curveSpeed F c z.2 z.1
  let W : ℝ × ℝ → ℝ := fun z => deriv (curveSpeed F c z.2) z.1
  let Ω : Set (ℝ × ℝ) := univ ×ˢ Ioo a b
  let D : Set (ℝ × ℝ) := univ ×ˢ Icc a s
  have hΩ : IsOpen Ω := isOpen_univ.prod isOpen_Ioo
  have hv : ContDiffOn ℝ ∞ v Ω := M62.speed_joint_contDiffOn F c hc
  have hdx (t : ℝ) (ht : t ∈ Ioo a b) (x : ℝ) :
      HasDerivAt (curveSpeed F c t) (M08.coordinatePartialS v (x, t)) x :=
    M08.coordinateSlice_fst_hasDerivAt v (p := (x, t))
      ((hv.contDiffAt (hΩ.mem_nhds ⟨mem_univ _, ht⟩)).differentiableAt (by simp))
  have hW : ContinuousOn W Ω :=
    ((M08.coordinatePartialS_contDiffOn hΩ v hv).congr
      (fun z hz => (hdx z.2 hz.2 z.1).deriv)).continuousOn
  have hzero (x : ℝ) : W (x, a) = 0 := by
    change deriv (curveSpeed F c a) x = 0
    rw [show curveSpeed F c a = (fun _ : ℝ => v0) from funext hInitial]
    exact deriv_const x v0
  let V := v0 * Real.exp ((K + R) * (b - a))
  let B : ℝ → ℝ := fun t => V ^ 2 *
    ((K + 2 * K * Real.sqrt R) * (t - a) +
      4 * Real.sqrt R * J * Real.sqrt (t - a))
  have hB : Continuous B := by dsimp only [B]; fun_prop
  have hBa : B a = 0 := by
    simp only [B, sub_self, Real.sqrt_zero, mul_zero, add_zero]
  have hbound (z : ℝ × ℝ) (hz : z ∈ D) : ‖W z‖ ≤ B z.2 := by
    rw [Real.norm_eq_abs]
    exact curveSpeed_spatial_abs_bound F c hc hK hR hJ hv0 hBounds hInitial hCurv hJet
      ⟨hz.2.1, hz.2.2.trans hsb.le⟩ z.1
  have hclosed : ContinuousOn W D := by
    intro z hz
    by_cases ht : a < z.2
    · exact (hW.continuousAt (hΩ.mem_nhds
        ⟨mem_univ _, ht, hz.2.2.trans_lt hsb⟩)).continuousWithinAt
    · have hta : z.2 = a := le_antisymm (le_of_not_gt ht) hz.2.1
      have hwz : W z = 0 := by
        change deriv (curveSpeed F c z.2) z.1 = 0
        rw [hta]
        exact hzero z.1
      have hlim : Tendsto (fun p : ℝ × ℝ => B p.2) (𝓝[D] z) (𝓝 0) := by
        have hcB : Continuous (fun p : ℝ × ℝ => B p.2) := hB.comp continuous_snd
        have hlim0 : Tendsto (fun p : ℝ × ℝ => B p.2) (𝓝[D] z) (𝓝 (B z.2)) :=
          hcB.continuousAt.continuousWithinAt
        simpa only [hta, hBa] using hlim0
      change Tendsto W (𝓝[D] z) (𝓝 (W z))
      rw [hwz]
      exact squeeze_zero_norm' (by
        filter_upwards [self_mem_nhdsWithin] with p hp
        exact hbound p hp) hlim
  have hper (t : Icc a s) :
      Function.Periodic (fun x => W (x, (t : ℝ))) curvePeriod := by
    have hp := M62.speed_periodic F c hc ⟨t.2.1, t.2.2.trans hsb.le⟩
    intro x
    change deriv (curveSpeed F c t) (x + curvePeriod) = deriv (curveSpeed F c t) x
    rw [← deriv_comp_add_const]
    exact congrArg (fun f : ℝ → ℝ => deriv f x) (funext hp)
  let Q : Icc a s → C(AddCircle curvePeriod, ℝ) := fun t =>
    ⟨(hper t).lift,
      (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples curvePeriod)).continuous_iff.mpr
        (hclosed.comp_continuous (continuous_id.prodMk continuous_const)
          (fun _ => ⟨mem_univ _, t.2⟩))⟩
  have hrep (t : Icc a s) (x : ℝ) : Q t (x : AddCircle curvePeriod) = W (x, t) := by
    simp only [Q, ContinuousMap.coe_mk, Function.Periodic.lift_coe]
  have hQ : Continuous Q := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    have hquot : IsOpenQuotientMap
        (fun p : Icc a s × ℝ => (p.1, (p.2 : AddCircle curvePeriod))) :=
      IsOpenQuotientMap.id.prodMap QuotientAddGroup.isOpenQuotientMap_mk
    apply hquot.continuous_comp_iff.mp
    have hcomp : Continuous (fun p : Icc a s × ℝ => W (p.2, (p.1 : ℝ))) :=
      hclosed.comp_continuous
        (continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst))
        (fun p => ⟨mem_univ _, p.1.2⟩)
    exact hcomp.congr (fun p => (hrep p.1 p.2).symm)
  exact ⟨⟨Q, hQ⟩, hrep⟩

end PoincareConjecture.M63
