import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Projection

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Geometry.Manifold

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [NormedAddCommGroup F] [NormedSpace Real F]
  [FiniteDimensional Real E] [FiniteDimensional Real F]

theorem exists_continuousLinearEquiv_prod_of_injective
    (L : E →L[Real] F) (hL : Function.Injective L) :
    ∃ A : (E × EuclideanSpace Real
        (Fin (Module.finrank Real F - Module.finrank Real E))) ≃L[Real] F,
      ∀ x, A (x, 0) = L x := by
  let P := LinearMap.range L.toLinearMap
  obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl P
  let B : E ≃ₗ[Real] P := LinearEquiv.ofInjective L.toLinearMap hL
  have hdim : Module.finrank Real Q = Module.finrank Real F - Module.finrank Real E := by
    have hd := Submodule.finrank_add_eq_of_isCompl hQ
    rw [← B.finrank_eq] at hd
    omega
  let C : EuclideanSpace Real
      (Fin (Module.finrank Real F - Module.finrank Real E)) ≃L[Real] Q :=
    ContinuousLinearEquiv.ofFinrankEq (by simpa using hdim.symm)
  let A := ((B.prodCongr C.toLinearEquiv).trans (P.prodEquivOfIsCompl Q hQ)).toContinuousLinearEquiv
  refine ⟨A, fun x => ?_⟩
  simp [A, B, Submodule.coe_prodEquivOfIsCompl']
  rfl

private theorem exists_partialDiffeomorph_of_contDiffOn
    {G H : Type*} [NormedAddCommGroup G] [NormedSpace Real G]
    [NormedAddCommGroup H] [NormedSpace Real H] [CompleteSpace G] [CompleteSpace H]
    {g : G -> H} {s : Set G} (hs : IsOpen s) (hg : ContDiffOn Real ∞ g s)
    {a : G} (ha : a ∈ s) (hb : Function.Bijective (fderiv Real g a)) :
    ∃ d : PartialDiffeomorph 𝓘(Real, G) 𝓘(Real, H) G H ∞,
      a ∈ d.source ∧ d.source ⊆ s ∧ (d : G -> H) = g := by
  let A := ContinuousLinearEquiv.ofBijective (fderiv Real g a)
    (LinearMap.ker_eq_bot.mpr hb.1) (LinearMap.range_eq_top.mpr hb.2)
  have hga : ContDiffAt Real ∞ g a := hg.contDiffAt (hs.mem_nhds ha)
  have hd : HasFDerivAt g A.toContinuousLinearMap a :=
    (hga.differentiableAt (by simp)).hasFDerivAt
  let U := s ∩ (fderiv Real g) ⁻¹'
    range (fun B : G ≃L[Real] H => B.toContinuousLinearMap)
  have hU : IsOpen U :=
    (hg.continuousOn_fderiv_of_isOpen hs (by simp)).isOpen_inter_preimage hs
      ContinuousLinearEquiv.isOpen
  let Q := hga.toOpenPartialHomeomorph g hd (by simp)
  let D := Q.restr U
  have hDs : D.source ⊆ U := fun _ hz => interior_subset hz.2
  have hDa : a ∈ D.source := by
    rw [Q.restr_source' U hU]
    exact ⟨hga.mem_toOpenPartialHomeomorph_source hd (by simp), ha, A, rfl⟩
  have hDi : ContMDiffOn 𝓘(Real, H) 𝓘(Real, G) ∞ D.symm D.target := by
    intro y hy
    have hz := hDs (D.map_target hy)
    obtain ⟨B, hB⟩ := hz.2
    dsimp only at hB
    have hgz : ContDiffAt Real ∞ g (D.symm y) := hg.contDiffAt (hs.mem_nhds hz.1)
    have hdB : HasFDerivAt D B.toContinuousLinearMap (D.symm y) := by
      change HasFDerivAt g B.toContinuousLinearMap (D.symm y)
      rw [hB]
      exact (hgz.differentiableAt (by simp)).hasFDerivAt
    exact (D.contDiffAt_symm hy hdB hgz).contMDiffWithinAt.mono (subset_univ _)
  let d : PartialDiffeomorph 𝓘(Real, G) 𝓘(Real, H) G H ∞ := {
    toPartialEquiv := D.toPartialEquiv
    open_source := D.open_source
    open_target := D.open_target
    contMDiffOn_toFun := (hg.mono (fun _ hz => (hDs hz).1)).contMDiffOn
    contMDiffOn_invFun := hDi }
  exact ⟨d, hDa, fun _ hz => (hDs hz).1, rfl⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(Real, E) ∞ M]

theorem isImmersionAtOfComplement_of_injective_mfderiv
    {f : M -> F} (hf : ContMDiff 𝓘(Real, E) 𝓘(Real, F) ∞ f) (x : M)
    (hinj : Function.Injective (mfderiv 𝓘(Real, E) 𝓘(Real, F) f x)) :
    _root_.Manifold.IsImmersionAtOfComplement
      (EuclideanSpace Real (Fin (Module.finrank Real F - Module.finrank Real E)))
      𝓘(Real, E) 𝓘(Real, F) ∞ f x := by
  let C := EuclideanSpace Real (Fin (Module.finrank Real F - Module.finrank Real E))
  let c := chartAt E x
  let g : E -> F := f ∘ c.symm
  have hg : ContDiffOn Real ∞ g c.target :=
    (hf.comp_contMDiffOn (contMDiffOn_chart_symm (I := 𝓘(Real, E)))).contDiffOn
  have hder : mfderiv 𝓘(Real, E) 𝓘(Real, F) f x = fderiv Real g (c x) := by
    rw [mfderiv, if_pos ((hf x).mdifferentiableAt (by simp))]
    simp [g, c, writtenInExtChartAt]
  obtain ⟨A, hA⟩ := exists_continuousLinearEquiv_prod_of_injective
    (fderiv Real g (c x)) (hder ▸ hinj)
  let G : E × C -> F := fun z => g z.1 + A (0, z.2)
  have hG : ContDiffOn Real ∞ G (c.target ×ˢ univ) :=
    (hg.comp contDiffOn_fst (fun _ hz => hz.1)).add
      (A.contDiff.comp (contDiff_const.prodMk contDiff_snd)).contDiffOn
  have hcx : c x ∈ c.target := c.map_source (mem_chart_source E x)
  have hdG : HasFDerivAt G A.toContinuousLinearMap (c x, 0) := by
    have hdg := (hg.contDiffAt (c.open_target.mem_nhds hcx)).differentiableAt (by simp)
    have hd := (hdg.hasFDerivAt.comp (c x, (0 : C)) hasFDerivAt_fst).add
      (A.hasFDerivAt.comp (c x, (0 : C))
        ((hasFDerivAt_const (0 : E) (c x, (0 : C))).prodMk hasFDerivAt_snd))
    have heq : A.toContinuousLinearMap =
        (fderiv Real g (c x)).comp (ContinuousLinearMap.fst Real E C) +
          A.toContinuousLinearMap.comp
            ((0 : E × C →L[Real] E).prod (ContinuousLinearMap.snd Real E C)) := by
      apply ContinuousLinearMap.ext
      intro z
      change A z = fderiv Real g (c x) z.1 + A (0, z.2)
      rw [← hA z.1, ← map_add]
      congr 1
      simp
    rw [heq]
    exact hd
  obtain ⟨d, hd0, hds, hdGfun⟩ := exists_partialDiffeomorph_of_contDiffOn
    (c.open_target.prod isOpen_univ) hG (show (c x, (0 : C)) ∈ c.target ×ˢ univ from ⟨hcx, trivial⟩)
      (by rw [hdG.fderiv]; exact A.bijective)
  let V : Set E := {u | (u, (0 : C)) ∈ d.source}
  have hV : IsOpen V := d.open_source.preimage (continuous_id.prodMk continuous_const)
  let a := (c.symm.restrOpen V hV).symm
  let b := d.symm.toOpenPartialHomeomorph.trans A.toHomeomorph.toOpenPartialHomeomorph
  have ham : a ∈ IsManifold.maximalAtlas 𝓘(Real, E) ∞ M := by
    apply a.mem_maximalAtlas_of_contMDiffOn
    · exact (contMDiffOn_chart (I := 𝓘(Real, E)) (x := x)).mono inter_subset_left
    · exact (contMDiffOn_chart_symm (I := 𝓘(Real, E)) (x := x)).mono inter_subset_left
  have hbm : b ∈ IsManifold.maximalAtlas 𝓘(Real, F) ∞ F := by
    apply b.mem_maximalAtlas_of_contMDiffOn
    · exact A.contDiff.contMDiff.comp_contMDiffOn
        (d.contMDiffOn_invFun.mono inter_subset_left)
    · exact d.contMDiffOn_toFun.comp A.symm.contDiff.contMDiff.contMDiffOn
        (fun _ hy => hy.2)
  have hax : x ∈ a.source := ⟨mem_chart_source E x, hd0⟩
  have hGzero (y : M) (hy : y ∈ c.source) : d (c y, 0) = f y := by
    rw [hdGfun]
    simp [G, g, c.left_inv hy]
  have hsource (y : M) (hy : y ∈ a.source) : f y ∈ b.source := by
    have hyD : (c y, (0 : C)) ∈ d.source := hy.2
    refine ⟨?_, mem_univ _⟩
    rw [← hGzero y hy.1]
    exact d.map_source hyD
  apply _root_.Manifold.IsImmersionAtOfComplement.mk_of_charts A a b hax
    (hsource x hax) ham hbm hsource
  intro u hu
  have hu' : u ∈ a.target := by simpa using hu
  have huD : (u, (0 : C)) ∈ d.source := hu'.2
  change A (d.symm (f (c.symm u))) = A (u, 0)
  have heq : f (c.symm u) = d (u, 0) := by
    rw [hdGfun]
    simp [G, g]
  rw [heq]
  exact congrArg A (d.left_inv huD)

theorem isImmersion_of_injective_mfderiv
    {f : M -> F} (hf : ContMDiff 𝓘(Real, E) 𝓘(Real, F) ∞ f)
    (hinj : ∀ x, Function.Injective (mfderiv 𝓘(Real, E) 𝓘(Real, F) f x)) :
    _root_.Manifold.IsImmersion 𝓘(Real, E) 𝓘(Real, F) ∞ f :=
  _root_.Manifold.IsImmersionOfComplement.isImmersion
    (fun x => isImmersionAtOfComplement_of_injective_mfderiv hf x (hinj x))

theorem isSmoothEmbedding_of_injective_mfderiv [CompactSpace M]
    {f : M -> F} (hf : ContMDiff 𝓘(Real, E) 𝓘(Real, F) ∞ f)
    (hfi : Function.Injective f)
    (hinj : ∀ x, Function.Injective (mfderiv 𝓘(Real, E) 𝓘(Real, F) f x)) :
    _root_.Manifold.IsSmoothEmbedding 𝓘(Real, E) 𝓘(Real, F) ∞ f :=
  ⟨isImmersion_of_injective_mfderiv hf hinj,
    (hf.continuous.isClosedEmbedding hfi).isEmbedding⟩

end Poincare.Geometry.Manifold
