import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.SaddleOrientationPrimitives
import PoincareConjecture.Proofs.M25.Topology3D.Space3.RegularLevelField

set_option autoImplicit false

open Set Filter Function
open scoped ContDiff Manifold InnerProductSpace Matrix Topology

namespace PoincareConjecture.M25.Topology3D.SaddleOrientation

private theorem immersed_columns_cross_ne_zero
    (T : (ℝ × ℝ) →L[ℝ] E3) (hT : Function.Injective T) :
    WithLp.ofLp (T (1, 0)) ⨯₃ WithLp.ofLp (T (0, 1)) ≠ 0 := by
  let e := EuclideanSpace.equiv (Fin 3) ℝ
  let F : (ℝ × ℝ) →L[ℝ] (Fin 3 → ℝ) := e.toContinuousLinearMap.comp T
  have hF : Function.Injective F := e.injective.comp hT
  change F (1, 0) ⨯₃ F (0, 1) ≠ 0
  apply crossProduct_ne_zero_iff_linearIndependent.mpr
  apply LinearIndependent.pair_iff.mpr
  intro a b hab
  have hp : (a, b) = a • ((1 : ℝ), 0) + b • ((0 : ℝ), 1) := by
    ext <;> simp
  have hz : F (a, b) = 0 := by
    calc
      F (a, b) = a • F (1, 0) + b • F (0, 1) := by
        rw [hp, map_add, map_smul, map_smul]
      _ = 0 := hab
  have hab0 : (a, b) = 0 := hF (hz.trans (map_zero F).symm)
  exact ⟨congrArg Prod.fst hab0, congrArg Prod.snd hab0⟩

private theorem continuousOn_dot_cross
    {X : Type*} [TopologicalSpace X] {S : Set X}
    (n e1 e2 : X → Fin 3 → ℝ)
    (hn : ContinuousOn n S) (h1 : ContinuousOn e1 S) (h2 : ContinuousOn e2 S) :
    ContinuousOn (fun s => n s ⬝ᵥ (e1 s ⨯₃ e2 s)) S := by
  have hn' (i : Fin 3) : ContinuousOn (fun s => n s i) S :=
    (continuous_apply i).comp_continuousOn hn
  have h1' (i : Fin 3) : ContinuousOn (fun s => e1 s i) S :=
    (continuous_apply i).comp_continuousOn h1
  have h2' (i : Fin 3) : ContinuousOn (fun s => e2 s i) S :=
    (continuous_apply i).comp_continuousOn h2
  have h0 := (hn' 0).mul
    (((h1' 1).mul (h2' 2)).sub ((h1' 2).mul (h2' 1)))
  have h1 := (hn' 1).mul
    (((h1' 2).mul (h2' 0)).sub ((h1' 0).mul (h2' 2)))
  have h2 := (hn' 2).mul
    (((h1' 0).mul (h2' 1)).sub ((h1' 1).mul (h2' 0)))
  convert (h0.add h1).add h2 using 1
  funext s
  simp only [cross_apply, Matrix.vec3_dotProduct, Matrix.cons_val,
    Pi.add_apply, Pi.sub_apply, Pi.mul_apply]

theorem collar_chart_orientation
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (rho : E3 → ℝ)
    (hrho : ContDiffOn ℝ ∞ rho (psi '' (univ ×ˢ Ioo (-1) 1)))
    (hrhopsi : ∀ p ∈ (univ ×ˢ Ioo (-1) 1 : Set (UnitTwoSphere × ℝ)),
      rho (psi p) = p.2)
    (hrhonz : ∀ y ∈ psi '' (univ ×ˢ Ioo (-1) 1), fderiv ℝ rho y ≠ 0)
    (M : OpenPartialHomeomorph (ℝ × ℝ) UnitTwoSphere)
    (hMs : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ M M.source)
    (hMi : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ × ℝ) ∞ M.symm M.target) :
    let A : (ℝ × ℝ) → E3 := fun s => psi (M s, 0)
    let Csign : (ℝ × ℝ) → ℝ := fun s =>
      WithLp.ofLp (gradient rho (A s)) ⬝ᵥ
        (WithLp.ofLp (fderiv ℝ A s (1, 0)) ⨯₃
          WithLp.ofLp (fderiv ℝ A s (0, 1)))
    ContDiffOn ℝ ∞ A M.source ∧
      (∀ s ∈ M.source, Function.Injective (fderiv ℝ A s)) ∧
      ContinuousOn Csign M.source ∧ (∀ s ∈ M.source, Csign s ≠ 0) ∧
      ∀ s ∈ M.source,
        ⟪gradient rho (A s), fderiv ℝ A s (1, 0)⟫_ℝ = 0 ∧
        ⟪gradient rho (A s), fderiv ℝ A s (0, 1)⟫_ℝ = 0 := by
  let j : UnitTwoSphere → E3 := fun p => psi (p, 0)
  let A : (ℝ × ℝ) → E3 := j ∘ M
  have hj := collar_central_contMDiff psi hpsi
  have hMD : M.MDifferentiable 𝓘(ℝ, ℝ × ℝ) (𝓡 2) :=
    ⟨hMs.mdifferentiableOn (by simp), hMi.mdifferentiableOn (by simp)⟩
  have hA : ContDiffOn ℝ ∞ A M.source :=
    (hj.comp_contMDiffOn hMs).contDiffOn
  have hAi (s : ℝ × ℝ) (hs : s ∈ M.source) :
      Injective (fderiv ℝ A s) := by
    have hd := (hj.mdifferentiable (by simp) (M s)).hasMFDerivAt.comp s
      (hMD.mdifferentiableAt hs).hasMFDerivAt
    have heq : fderiv ℝ A s =
        (mfderiv (𝓡 2) 𝓘(ℝ, E3) j (M s)).comp
          (mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓡 2) M s) := by
      have hh := hd.mfderiv
      rw [mfderiv_eq_fderiv] at hh
      exact hh
    rw [heq]
    exact (collar_central_mfderiv_injective psi hpsi (M s)).comp
      (hMD.mfderiv_injective hs)
  let U := psi '' (univ ×ˢ Ioo (-1) 1)
  have hU : IsOpen U := collar_image_open psi hpsi
  have hAU (s : ℝ × ℝ) : A s ∈ U :=
    ⟨(M s, 0), ⟨mem_univ _, by norm_num⟩, rfl⟩
  have hzero : rho ∘ A = fun _ => (0 : ℝ) := by
    funext s
    exact hrhopsi (M s, 0) ⟨mem_univ _, by norm_num⟩
  have horth (s : ℝ × ℝ) (hs : s ∈ M.source) :
      ⟪gradient rho (A s), fderiv ℝ A s (1, 0)⟫_ℝ = 0 ∧
      ⟪gradient rho (A s), fderiv ℝ A s (0, 1)⟫_ℝ = 0 := by
    have hr := (hrho.contDiffAt (hU.mem_nhds (hAU s))).differentiableAt (by simp)
    have ha := (hA.contDiffAt (M.open_source.mem_nhds hs)).differentiableAt (by simp)
    have hd := (hr.hasFDerivAt.comp s ha.hasFDerivAt).fderiv
    rw [hzero, fderiv_const_apply] at hd
    constructor
    · rw [inner_gradient_left]
      exact congrArg (fun L => L (1, 0)) hd.symm
    · rw [inner_gradient_left]
      exact congrArg (fun L => L (0, 1)) hd.symm
  let coord := EuclideanSpace.equiv (Fin 3) ℝ
  let normal : (ℝ × ℝ) → Fin 3 → ℝ := fun s => coord (gradient rho (A s))
  let col1 : (ℝ × ℝ) → Fin 3 → ℝ := fun s => coord (fderiv ℝ A s (1, 0))
  let col2 : (ℝ × ℝ) → Fin 3 → ℝ := fun s => coord (fderiv ℝ A s (0, 1))
  let Csign : (ℝ × ℝ) → ℝ := fun s => normal s ⬝ᵥ (col1 s ⨯₃ col2 s)
  have hd : ContinuousOn (fderiv ℝ A) M.source :=
    hA.continuousOn_fderiv_of_isOpen M.open_source (by simp)
  have hnormal : ContinuousOn normal M.source :=
    coord.continuous.comp_continuousOn
      ((contDiffOn_gradient_of_isOpen hU rho hrho).continuousOn.comp
        hA.continuousOn (fun s _ => hAU s))
  have hcol1 : ContinuousOn col1 M.source :=
    coord.continuous.comp_continuousOn (hd.clm_apply continuousOn_const)
  have hcol2 : ContinuousOn col2 M.source :=
    coord.continuous.comp_continuousOn (hd.clm_apply continuousOn_const)
  have hCcont : ContinuousOn Csign M.source :=
    continuousOn_dot_cross normal col1 col2 hnormal hcol1 hcol2
  have hCne (s : ℝ × ℝ) (hs : s ∈ M.source) : Csign s ≠ 0 := by
    have hn : normal s ≠ 0 := by
      intro hz
      have hz' : gradient rho (A s) = 0 :=
        coord.injective (hz.trans (map_zero coord).symm)
      apply hrhonz (A s) (hAU s)
      rw [← toDual_gradient, hz', map_zero]
    have hc : col1 s ⨯₃ col2 s ≠ 0 :=
      immersed_columns_cross_ne_zero (fderiv ℝ A s) (hAi s hs)
    have hn1 : col1 s ⬝ᵥ normal s = 0 := by
      have hh := (horth s hs).1
      rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] at hh
      exact hh
    have hn2 : col2 s ⬝ᵥ normal s = 0 := by
      have hh := (horth s hs).2
      rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] at hh
      exact hh
    change normal s ⬝ᵥ (col1 s ⨯₃ col2 s) ≠ 0
    rw [triple_product_permutation]
    exact triple_ne_zero_of_transverse (col1 s) (col2 s) (normal s) hc hn hn1 hn2
  exact ⟨hA, hAi, hCcont, hCne, horth⟩

end PoincareConjecture.M25.Topology3D.SaddleOrientation
