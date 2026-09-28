import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.ContinuousDependenceEmbeddedJets
import PoincareConjecture.Proofs.M63.Mathlib.PeriodicSmoothApproximation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u v w

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {ι : Type v} [Fintype ι] {Z : Type w} [TopologicalSpace Z]

local notation "W" => EuclideanSpace ℝ ι
local notation "Y" => C(AddCircle curvePeriod, (W × W) × W)

theorem exists_compact_initialJet_image [CompactSpace Z]
    (gamma : Z → ℝ → M)
    (hperiod : ∀ z, Function.Periodic (gamma z) curvePeriod)
    (hC2 : ∀ z, ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 (gamma z))
    (himm : ∀ z x, curveVelocity (n := n) (gamma z) x ≠ 0)
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {ρ : W → M} (hρe : ∀ p, ρ (e p) = p)
    (hzero : Continuous (fun z : Z × ℝ => e (gamma z.1 z.2)))
    (hfirst : Continuous (fun z : Z × ℝ =>
      deriv (fun y => e (gamma z.1 y)) z.2))
    (hsecond : Continuous (fun z : Z × ℝ =>
      deriv (deriv (fun y => e (gamma z.1 y))) z.2)) :
    ∃ J : C(Z, Y),
      IsCompact (range (J : Z → Y)) ∧
      (∀ z (x : ℝ), J z (x : AddCircle curvePeriod) =
        ((e (gamma z x), deriv (fun y => e (gamma z y)) x),
          deriv (deriv (fun y => e (gamma z y))) x)) ∧
      let K := range (J : Z → Y)
      let gammaK : K → ℝ → M := fun k x =>
        ρ ((k.1 (x : AddCircle curvePeriod)).1.1)
      (∀ k : K,
        Function.Periodic (gammaK k) curvePeriod ∧
        ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 (gammaK k) ∧
        (∀ x, curveVelocity (n := n) (gammaK k) x ≠ 0) ∧
        (∀ x, e (gammaK k x) = (k.1 (x : AddCircle curvePeriod)).1.1) ∧
        (∀ x : ℝ, HasDerivAt (fun y : ℝ => e (gammaK k y))
          (k.1 (x : AddCircle curvePeriod)).1.2 x) ∧
        (∀ x : ℝ, HasDerivAt (deriv (fun y : ℝ => e (gammaK k y)))
          (k.1 (x : AddCircle curvePeriod)).2 x) ∧
        (∀ x, deriv (fun y : ℝ => e (gammaK k y)) x =
          (k.1 (x : AddCircle curvePeriod)).1.2) ∧
        (∀ x, deriv (deriv (fun y : ℝ => e (gammaK k y))) x =
          (k.1 (x : AddCircle curvePeriod)).2)) ∧
      Continuous (fun p : K × ℝ => e (gammaK p.1 p.2)) ∧
      Continuous (fun p : K × ℝ => deriv (fun y => e (gammaK p.1 y)) p.2) ∧
      Continuous (fun p : K × ℝ =>
        deriv (deriv (fun y => e (gammaK p.1 y))) p.2) ∧
      (∀ z (x : ℝ), gammaK (⟨J z, mem_range_self z⟩ : K) x = gamma z x) := by
  classical
  let : Fact (0 < curvePeriod) := ⟨by unfold curvePeriod; positivity⟩
  let f : Z → ℝ → W := fun z x => e (gamma z x)
  have hf (z : Z) : ContDiff ℝ 2 (f z) :=
    ((he.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).comp (hC2 z)).contDiff
  have hfper (z : Z) : Function.Periodic (f z) curvePeriod :=
    fun x => congrArg e (hperiod z x)
  have hpper (z : Z) : Function.Periodic (deriv (f z)) curvePeriod :=
    (hfper z).deriv_of_differentiable ((hf z).differentiable (by norm_num))
  have hrper (z : Z) : Function.Periodic (deriv (deriv (f z))) curvePeriod :=
    (hpper z).deriv_of_differentiable
      (((hf z).deriv' (n := 1)).differentiable (by norm_num))
  let q : Z → ℝ → (W × W) × W := fun z x =>
    ((f z x, deriv (f z) x), deriv (deriv (f z)) x)
  have hq : Continuous (fun z : Z × ℝ => q z.1 z.2) :=
    (hzero.prodMk hfirst).prodMk hsecond
  have hqper (z : Z) : Function.Periodic (q z) curvePeriod := fun x =>
    Prod.ext (Prod.ext (hfper z x) (hpper z x)) (hrper z x)
  let J0 : Z → Y := fun z => ⟨(hqper z).lift,
    (QuotientAddGroup.isQuotientMap_mk
      (AddSubgroup.zmultiples curvePeriod)).continuous_iff.mpr
        (hq.comp (continuous_const.prodMk continuous_id))⟩
  have hrep0 (z : Z) (x : ℝ) : J0 z (x : AddCircle curvePeriod) = q z x := by
    change (hqper z).lift (x : AddCircle curvePeriod) = q z x
    exact Function.Periodic.lift_coe (hqper z) x
  have hJ0 : Continuous J0 := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    have hquot : IsOpenQuotientMap
        (fun z : Z × ℝ => (z.1, (z.2 : AddCircle curvePeriod))) :=
      IsOpenQuotientMap.id.prodMap QuotientAddGroup.isOpenQuotientMap_mk
    apply hquot.continuous_comp_iff.mp
    simpa only [Function.comp_def, Function.uncurry, hrep0] using hq
  let J : C(Z, Y) := ⟨J0, hJ0⟩
  have hrep (z : Z) (x : ℝ) : J z (x : AddCircle curvePeriod) =
      ((e (gamma z x), deriv (fun y => e (gamma z y)) x),
        deriv (deriv (fun y => e (gamma z y))) x) := hrep0 z x
  let K := range (J : Z → Y)
  let gammaK : K → ℝ → M := fun k x =>
    ρ ((k.1 (x : AddCircle curvePeriod)).1.1)
  have hdata (k : K) :
      Function.Periodic (gammaK k) curvePeriod ∧
      ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 (gammaK k) ∧
      (∀ x, curveVelocity (n := n) (gammaK k) x ≠ 0) ∧
      (∀ x, e (gammaK k x) = (k.1 (x : AddCircle curvePeriod)).1.1) ∧
      (∀ x : ℝ, HasDerivAt (fun y : ℝ => e (gammaK k y))
        (k.1 (x : AddCircle curvePeriod)).1.2 x) ∧
      (∀ x : ℝ, HasDerivAt (deriv (fun y : ℝ => e (gammaK k y)))
        (k.1 (x : AddCircle curvePeriod)).2 x) ∧
      (∀ x, deriv (fun y : ℝ => e (gammaK k y)) x =
        (k.1 (x : AddCircle curvePeriod)).1.2) ∧
      (∀ x, deriv (deriv (fun y : ℝ => e (gammaK k y))) x =
        (k.1 (x : AddCircle curvePeriod)).2) := by
    obtain ⟨z, hz⟩ := k.2
    have hk : gammaK k = gamma z := by
      funext x
      change ρ ((k.1 (x : AddCircle curvePeriod)).1.1) = gamma z x
      rw [← hz, hrep]
      exact hρe _
    have hd (x : ℝ) : HasDerivAt (fun y : ℝ => e (gammaK k y))
        (k.1 (x : AddCircle curvePeriod)).1.2 x := by
      rw [hk, ← hz, hrep]
      exact ((hf z).differentiable (by norm_num) x).hasDerivAt
    have hdd (x : ℝ) : HasDerivAt (deriv (fun y : ℝ => e (gammaK k y)))
        (k.1 (x : AddCircle curvePeriod)).2 x := by
      rw [hk, ← hz, hrep]
      exact (((hf z).deriv' (n := 1)).differentiable (by norm_num) x).hasDerivAt
    refine ⟨hk.symm ▸ hperiod z, hk.symm ▸ hC2 z, ?_, ?_, hd, hdd,
      fun x => (hd x).deriv, fun x => (hdd x).deriv⟩
    · exact hk.symm ▸ himm z
    · intro x
      rw [hk, ← hz, hrep]
  have heval : Continuous
      (fun p : K × ℝ => p.1.1 (p.2 : AddCircle curvePeriod)) :=
    (continuous_subtype_val.comp continuous_fst).eval
      ((AddCircle.continuous_mk' curvePeriod).comp continuous_snd)
  refine ⟨J, isCompact_range J.continuous, hrep, hdata, ?_, ?_, ?_, ?_⟩
  · exact heval.fst.fst.congr (fun p => ((hdata p.1).2.2.2.1 p.2).symm)
  · exact heval.fst.snd.congr (fun p => ((hdata p.1).2.2.2.2.2.2.1 p.2).symm)
  · exact heval.snd.congr (fun p => ((hdata p.1).2.2.2.2.2.2.2 p.2).symm)
  · intro z x
    change ρ ((J z (x : AddCircle curvePeriod)).1.1) = gamma z x
    rw [hrep]
    exact hρe _

end PoincareConjecture.M63
