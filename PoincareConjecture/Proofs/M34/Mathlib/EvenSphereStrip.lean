import PoincareConjecture.Proofs.M34.Mathlib.EvenMapDeterminant
import PoincareConjecture.Proofs.M34.Mathlib.SmoothRadialCoordinates
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv











set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M34





theorem not_even_sphere_strip_immersion
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]
    (H : sphere (0 : E) 1 × ℝ → E)
    (hH : ContMDiffOn ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) 1 H
      (univ ×ˢ Ioo (-1 : ℝ) 1))
    (hinj : ∀ p ∈ univ ×ˢ Ioo (-1 : ℝ) 1,
      Function.Injective (mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) H p))
    (heven : ∀ p ∈ univ ×ˢ Ioo (-1 : ℝ) 1, H (-p.1, p.2) = H p)
    (hconnected : IsPreconnected (sphere (0 : E) 1))
    (hdim : Odd (Module.finrank ℝ E)) {a : E} (ha : ‖a‖ = 1) : False := by
  classical
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  let a' : ({0}ᶜ : Set E) := ⟨a, ha0⟩
  let : Nonempty ({0}ᶜ : Set E) := ⟨a'⟩
  have hpuncture : IsOpen ({0}ᶜ : Set E) := isOpen_compl_singleton
  let := hpuncture.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hpuncture.isOpenEmbedding_subtypeVal.isManifold_singleton
    (I := 𝓘(ℝ, E)) (n := ∞)
  let c := extChartAt 𝓘(ℝ, E) a'
  let g := radialSphereCoordinates ∘ c.symm
  let f := H ∘ g
  let U : Set E := {x | 1 / 2 < ‖x‖ ∧ ‖x‖ < 3 / 2}
  have hU : IsOpen U :=
    (isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)
  have hnonzero (x : E) (hx : x ∈ U) : x ∈ ({0}ᶜ : Set E) := by
    have hpos : 0 < ‖x‖ := lt_trans (by norm_num) hx.1
    exact norm_pos_iff.mp hpos
  have hval (x : E) (hx : x ∈ U) : (c.symm x : E) = x :=
    canonicalOpen_chart_coe_symm isOpen_compl_singleton a' x (hnonzero x hx)
  have hnegative (x : E) (hx : x ∈ U) : -x ∈ U := by
    simpa only [U, mem_ofPred_eq, norm_neg] using hx
  have hstrip (x : E) (hx : x ∈ U) : g x ∈ univ ×ˢ Ioo (-1 : ℝ) 1 := by
    refine ⟨mem_univ _, ?_⟩
    change -1 < ‖(c.symm x : E)‖ - 1 ∧ ‖(c.symm x : E)‖ - 1 < 1
    rw [hval x hx]
    constructor <;> linarith [hx.1, hx.2]
  have hc (x : E) (hx : x ∈ U) :
      ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ c.symm x :=
    canonicalOpen_contMDiffAt_symm isOpen_compl_singleton a' x (hnonzero x hx)
  have hg (x : E) (hx : x ∈ U) :
      ContMDiffAt 𝓘(ℝ, E) ((𝓡 n).prod 𝓘(ℝ, ℝ)) ∞ g x :=
    (contMDiff_radialSphereCoordinates (n := n) (c.symm x)).comp x (hc x hx)
  have hh (x : E) (hx : x ∈ U) :
      ContMDiffAt ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) 1 H (g x) :=
    (hH (g x) (hstrip x hx)).contMDiffAt
      ((isOpen_univ.prod isOpen_Ioo).mem_nhds (hstrip x hx))
  have hf : ContDiffOn ℝ 1 f U := by
    intro x hx
    exact ((hh x hx).comp x ((hg x hx).of_le (by simp))).contDiffAt.contDiffWithinAt
  have hfinj (x : E) (hx : x ∈ U) : Function.Injective (fderiv ℝ f x) := by
    have hcg := mfderiv_comp x
      ((contMDiff_radialSphereCoordinates (n := n) (m := ∞) (c.symm x)).mdifferentiableAt
        (by simp))
      ((hc x hx).mdifferentiableAt (by simp))
    have hcf := mfderiv_comp x ((hh x hx).mdifferentiableAt (by simp))
      ((hg x hx).mdifferentiableAt (by simp))
    change Function.Injective (fderiv ℝ (H ∘ g) x)
    rw [← mfderiv_eq_fderiv, hcf]
    apply (hinj (g x) (hstrip x hx)).comp
    change Function.Injective
      (mfderiv 𝓘(ℝ, E) ((𝓡 n).prod 𝓘(ℝ, ℝ))
        (radialSphereCoordinates ∘ c.symm) x)
    rw [hcg, canonicalOpen_mfderiv_symm isOpen_compl_singleton a' x (hnonzero x hx)]
    exact (radialSphereCoordinates_mfderiv_injective (n := n) (c.symm x)).comp
      (Function.injective_id)
  have hK : sphere (0 : E) 1 ⊆ U := by
    intro x hx
    have hxnorm : ‖x‖ = 1 := by simpa using hx
    change 1 / 2 < ‖x‖ ∧ ‖x‖ < 3 / 2
    rw [hxnorm]
    norm_num
  have haK : a ∈ sphere (0 : E) 1 := by simpa using ha
  have hnaK : -a ∈ sphere (0 : E) 1 := by simpa using ha
  have hfeven : (fun x => f (-x)) =ᶠ[𝓝 a] f := by
    filter_upwards [hU.mem_nhds (hK haK)] with x hx
    have hradial : g (-x) = (-(g x).1, (g x).2) := by
      apply Prod.ext
      · apply Subtype.ext
        change ‖(c.symm (-x) : E)‖⁻¹ • (c.symm (-x) : E) =
          -(‖(c.symm x : E)‖⁻¹ • (c.symm x : E))
        rw [hval (-x) (hnegative x hx), hval x hx, norm_neg, smul_neg]
      · change ‖(c.symm (-x) : E)‖ - 1 = ‖(c.symm x : E)‖ - 1
        rw [hval (-x) (hnegative x hx), hval x hx, norm_neg]
    change H (g (-x)) = H (g x)
    rw [hradial]
    exact heven (g x) (hstrip x hx)
  obtain ⟨x, hx, hsingular⟩ := exists_not_injective_fderiv_of_eventually_even
    hU hconnected hK haK hnaK hf hdim hfeven
  exact hsingular (hfinj x (hK hx))

end PoincareConjecture.M34
