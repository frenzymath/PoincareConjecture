import PoincareConjecture.Proofs.M63.Mathlib.SpatialPartialDerivative
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.AmbientCurveCoefficients
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2GaugeWitnesses
import PoincareConjecture.Proofs.M62.Lemma0_1_Speed
import Mathlib.Analysis.Calculus.Deriv.Shift











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u v

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {a b : ℝ}

local notation "W" => EuclideanSpace ℝ ι




theorem ambientCurve_labelVelocity_regular (F : RicciFlow n M (Icc a b))
    {U : Set W} (hU : IsOpen U) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ U)
    {T L : ℝ} (hT : 0 < T) (hTb : a + T ≤ b) {q : ℝ → ℝ → W}
    (hq : ContDiffOn ℝ ∞ (Function.uncurry q) (Icc 0 T ×ˢ univ))
    (hper : ∀ t ∈ Icc 0 T, Function.Periodic (q t) L)
    (hguard : ∀ t ∈ Icc 0 T, ∀ x, q t x ∈ U ∧
      mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (q t x) (deriv (q t) x) ≠ 0) :
    let A := fun t x => ambientCurvePrincipal F ρ (a + t) (q t x) (deriv (q t) x)
    let w := fun t x => deriv (A t) x / 2
    ContDiffOn ℝ ∞ (Function.uncurry w) (Icc 0 T ×ˢ univ) ∧
      ∀ t ∈ Icc 0 T, Function.Periodic (w t) L := by
  let A := fun t x => ambientCurvePrincipal F ρ (a + t) (q t x) (deriv (q t) x)
  have hqx := contDiffOn_spatial_deriv_of_uniqueDiffOn (uniqueDiffOn_Icc hT)
    (m := ∞) (by simp) hq
  have hparam : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ =>
      ((a + z.1, q z.1 z.2), deriv (q z.1) z.2)) (Icc 0 T ×ˢ univ) :=
    ((contDiffOn_const.add contDiffOn_fst).prodMk hq).prodMk hqx
  have hmap : MapsTo (fun z : ℝ × ℝ =>
      ((a + z.1, q z.1 z.2), deriv (q z.1) z.2)) (Icc 0 T ×ˢ univ)
      {z : (ℝ × W) × W | z.1.1 ∈ Icc a b ∧ z.1.2 ∈ U ∧
        mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1.2 z.2 ≠ 0} := by
    intro z hz
    exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, hguard z.1 hz.1 z.2⟩
  have hA : ContDiffOn ℝ ∞ (Function.uncurry A) (Icc 0 T ×ˢ univ) :=
    (ambientCurveCoefficients_contDiffOn F (e := fun _ => 0) contMDiff_const hU hρ).1.comp
      hparam hmap
  have hAx := contDiffOn_spatial_deriv_of_uniqueDiffOn (uniqueDiffOn_Icc hT)
    (m := ∞) (by simp) hA
  refine ⟨hAx.div_const 2, ?_⟩
  intro t ht x
  have hqxper : Function.Periodic (deriv (q t)) L := by
    intro y
    rw [← deriv_comp_add_const, show (fun z => q t (z + L)) = q t from funext (hper t ht)]
  have hAper : Function.Periodic (A t) L := by
    intro y
    dsimp only [A]
    rw [hper t ht y, hqxper y]
  change deriv (A t) (x + L) / 2 = deriv (A t) x / 2
  rw [← deriv_comp_add_const, show (fun y => A t (y + L)) = A t from funext hAper]




theorem ambientCurve_labelVelocity_eq (F : RicciFlow n M (Icc a b))
    {U : Set W} (hU : IsOpen U) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ U) (t : ℝ)
    {f : ℝ → W} (hf : ContDiff ℝ 2 f)
    (hguard : ∀ x, f x ∈ U ∧ mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (f x) (deriv f x) ≠ 0) :
    let c := fun y (_ : ℝ) => ρ (f y)
    let A := fun x => ambientCurvePrincipal F ρ t (f x) (deriv f x)
    let v := curveSpeed F c t
    ∀ x, deriv A x / 2 = -(deriv v x / v x ^ 3) := by
  let c := fun y (_ : ℝ) => ρ (f y)
  let A := fun x => ambientCurvePrincipal F ρ t (f x) (deriv f x)
  let v := curveSpeed F c t
  change ∀ x, deriv A x / 2 = -(deriv v x / v x ^ 3)
  have hspace : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 (fun y => c y t) :=
    (hρ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).comp_contMDiff
      hf.contMDiff (fun x => (hguard x).1)
  have hvel (x : ℝ) : curveVelocity (n := n) (fun y => c y t) x =
      mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (f x) (deriv f x) := by
    change (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (ρ ∘ f) x) 1 = _
    erw [mfderiv_comp x
      ((hρ.contMDiffAt (hU.mem_nhds (hguard x).1)).mdifferentiableAt (by simp))
      ((hf.contMDiff x).mdifferentiableAt (by norm_num)),
      ContinuousLinearMap.comp_apply, mfderiv_eq_fderiv]
    rfl
  have himm (x : ℝ) : curveVelocity (n := n) (fun y => c y t) x ≠ 0 := by
    rw [hvel]
    exact (hguard x).2
  have hv : ContDiff ℝ 1 v := speed_contDiff_of_c2 F c hspace himm
  have hvpos (x : ℝ) : 0 < v x := Real.sqrt_pos.mpr ((F.metric t).pos _ _ (himm x))
  have hA : A = fun y => (v y ^ 2)⁻¹ := by
    funext y
    dsimp only [A, ambientCurvePrincipal]
    rw [← hvel y]
    exact congrArg (fun z : ℝ => z⁻¹) (M62.speed_sq F c t y).symm
  intro x
  have hne : v x ≠ 0 := (hvpos x).ne'
  have hd : HasDerivAt A (-2 * deriv v x / v x ^ 3) x := by
    rw [hA]
    convert! (((hv.differentiable (by simp) x).hasDerivAt.pow 2).inv
      (pow_ne_zero 2 (hvpos x).ne')) using 1
    simp only [Pi.pow_apply]
    field_simp [hne]
    ring
  change deriv A x / 2 = -(deriv v x / v x ^ 3)
  rw [hd.deriv]
  ring

end PoincareConjecture.M63
