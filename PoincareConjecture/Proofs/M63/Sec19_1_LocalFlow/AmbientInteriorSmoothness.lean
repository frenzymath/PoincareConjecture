import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.AmbientCompactJetBounds
import PoincareConjecture.Proofs.M63.Mathlib.ParabolicSpatialJetSmoothness

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

theorem ambientCurve_contDiffOn_infty (F : RicciFlow n M (Icc a b))
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ U)
    {T : ℝ} (hTb : a + T ≤ b) {q : ℝ → ℝ → W}
    (hspace : ∀ t ∈ Ioo 0 T, ContDiff ℝ ∞ (q t))
    (hjets : ∀ k : ℕ, ContinuousOn
      (fun z : ℝ × ℝ => iteratedDeriv k (q z.1) z.2) (Ioo 0 T ×ˢ univ))
    (hguard : ∀ t ∈ Ioo 0 T, ∀ x, q t x ∈ U ∧
      mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (q t x) (deriv (q t) x) ≠ 0)
    (htime : ∀ t ∈ Ioo 0 T, ∀ x, HasDerivAt (fun r => q r x)
      (ambientCurvePrincipal F ρ (a + t) (q t x) (deriv (q t) x) •
          iteratedDeriv 2 (q t) x +
        ambientCurveLower F e ρ (a + t) (q t x) (deriv (q t) x)) t) :
    ContDiffOn ℝ ∞ (Function.uncurry q) (Ioo 0 T ×ˢ univ) := by
  let Ω : Set (W × W) :=
    {z | z.1 ∈ U ∧ mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1 z.2 ≠ 0}
  let V : Set (ℝ × (W × (W × W))) :=
    {z | z.1 ∈ Ioo 0 T ∧ (z.2.1, z.2.2.1) ∈ Ω}
  let Φ : (ℝ × (W × (W × W))) → W := fun z =>
    ambientCurvePrincipal F ρ (a + z.1) z.2.1 z.2.2.1 • z.2.2.2 +
      ambientCurveLower F e ρ (a + z.1) z.2.1 z.2.2.1
  have hΩ : IsOpen Ω := isOpen_ambientCurveJetDomain F hU hρ
  have hV : IsOpen V :=
    (isOpen_Ioo.preimage continuous_fst).inter
      (hΩ.preimage (continuous_snd.fst.prodMk continuous_snd.snd.fst))
  have hparam : ContDiff ℝ ∞
      (fun z : ℝ × (W × (W × W)) => ((a + z.1, z.2.1), z.2.2.1)) := by
    fun_prop
  have hmap : MapsTo (fun z : ℝ × (W × (W × W)) =>
      ((a + z.1, z.2.1), z.2.2.1)) V
      {z : (ℝ × W) × W | z.1.1 ∈ Icc a b ∧ z.1.2 ∈ U ∧
        mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1.2 z.2 ≠ 0} := by
    intro z hz
    exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, hz.2⟩
  obtain ⟨hA, hB, _⟩ := ambientCurveCoefficients_contDiffOn F he hU hρ
  have hAc := hA.comp (s := V) hparam.contDiffOn hmap
  have hBc := hB.comp (s := V) hparam.contDiffOn hmap
  have hlast : ContDiffOn ℝ ∞
      (fun z : ℝ × (W × (W × W)) => z.2.2.2) V :=
    contDiff_snd.snd.snd.contDiffOn
  have hΦ : ContDiffOn ℝ ∞ Φ V := (hAc.smul hlast).add hBc
  exact contDiffOn_infty_of_spatial_jets_and_equation hV hΦ hspace hjets
    (fun t ht x => ⟨ht, hguard t ht x⟩) htime

end PoincareConjecture.M63
