import Mathlib.Geometry.Manifold.LocalDiffeomorph



set_option autoImplicit false

open Set
open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
  {E₃ : Type*} [NormedAddCommGroup E₃] [NormedSpace 𝕜 E₃]
  {E₄ : Type*} [NormedAddCommGroup E₄] [NormedSpace 𝕜 E₄]
  {H₁ : Type*} [TopologicalSpace H₁] {H₂ : Type*} [TopologicalSpace H₂]
  {H₃ : Type*} [TopologicalSpace H₃] {H₄ : Type*} [TopologicalSpace H₄]
  {I₁ : ModelWithCorners 𝕜 E₁ H₁} {I₂ : ModelWithCorners 𝕜 E₂ H₂}
  {I₃ : ModelWithCorners 𝕜 E₃ H₃} {I₄ : ModelWithCorners 𝕜 E₄ H₄}
  {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
  {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
  {M₃ : Type*} [TopologicalSpace M₃] [ChartedSpace H₃ M₃]
  {M₄ : Type*} [TopologicalSpace M₄] [ChartedSpace H₄ M₄]
  {n : ℕ∞ω}


theorem IsLocalDiffeomorphAt.prodMap {f : M₁ → M₂} {g : M₃ → M₄}
    {x : M₁} {y : M₃} (hf : IsLocalDiffeomorphAt I₁ I₂ n f x)
    (hg : IsLocalDiffeomorphAt I₃ I₄ n g y) :
    IsLocalDiffeomorphAt (I₁.prod I₃) (I₂.prod I₄) n (Prod.map f g) (x, y) := by
  obtain ⟨Φ, hx, hΦ⟩ := hf
  obtain ⟨Ψ, hy, hΨ⟩ := hg
  let e : PartialDiffeomorph (I₁.prod I₃) (I₂.prod I₄)
      (M₁ × M₃) (M₂ × M₄) n := {
    toPartialEquiv := Φ.toPartialEquiv.prod Ψ.toPartialEquiv
    open_source := Φ.open_source.prod Ψ.open_source
    open_target := Φ.open_target.prod Ψ.open_target
    contMDiffOn_toFun := Φ.contMDiffOn_toFun.prodMap Ψ.contMDiffOn_toFun
    contMDiffOn_invFun := Φ.contMDiffOn_invFun.prodMap Ψ.contMDiffOn_invFun }
  refine ⟨e, ⟨hx, hy⟩, ?_⟩
  intro z hz
  exact Prod.ext (hΦ hz.1) (hΨ hz.2)


theorem IsLocalDiffeomorph.prodMap {f : M₁ → M₂} {g : M₃ → M₄}
    (hf : IsLocalDiffeomorph I₁ I₂ n f) (hg : IsLocalDiffeomorph I₃ I₄ n g) :
    IsLocalDiffeomorph (I₁.prod I₃) (I₂.prod I₄) n (Prod.map f g) :=
  fun z => (hf z.1).prodMap (hg z.2)
