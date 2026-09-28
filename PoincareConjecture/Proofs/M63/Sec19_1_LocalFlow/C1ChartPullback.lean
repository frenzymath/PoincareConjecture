import PoincareConjecture.Proofs.M62.Sec19_1_PullbackTorsion











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M63

open Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)




theorem chartVectorField_param_contMDiff_one (p : M) (v : ℝ → E) (U : Set ℝ)
    (hv : ContDiffOn ℝ 1 v U) :
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 n)) ((𝓡 n).prod (𝓡 n)) 1
      (fun z : ℝ × M => Bundle.TotalSpace.mk' E z.2 (chartVectorField p (v z.1) z.2))
      (U ×ˢ (chartAt E p).source) := by
  have hp : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 n)) ((𝓡 n).prod (𝓡 n)) 1
      (fun z : ℝ × M => ((chartAt E p) z.2, v z.1)) (U ×ˢ (chartAt E p).source) :=
    (contMDiffOn_chart.comp contMDiff_snd.contMDiffOn (fun z hz => hz.2)).prodMk
      (hv.contMDiffOn.comp contMDiff_fst.contMDiffOn (fun z hz => hz.1))
  have htv : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 n)) ((𝓡 n).prod (𝓡 n)) 1
      (fun z : ℝ × M => (⟨(chartAt E p) z.2, v z.1⟩ : TangentBundle (𝓡 n) E))
      (U ×ˢ (chartAt E p).source) := by
    have hmodel : ContMDiff ((𝓡 n).prod (𝓡 n)) ((𝓡 n).prod (𝓡 n)) 1
        (fun q : E × E => (⟨q.1, q.2⟩ : TangentBundle (𝓡 n) E)) := by
      convert! (contMDiff_tangentBundleModelSpaceHomeomorph_symm (I := 𝓡 n) (n := 1)) using 1
      rw [chartedSpaceSelf_prod]
      rfl
    exact hmodel.comp_contMDiffOn hp
  have hc : ContMDiffOn (𝓡 n) (𝓡 n) 2 (chartAt E p).symm (chartAt E p).target :=
    contMDiffOn_chart_symm
  have ht := hc.contMDiffOn_tangentMapWithin (m := 1) (by norm_num)
    (chartAt E p).open_target.uniqueMDiffOn
  have h := ht.comp htv (fun z hz => (chartAt E p).map_source hz.2)
  apply h.congr
  intro z hz
  change Bundle.TotalSpace.mk' E z.2 (chartVectorField p (v z.1) z.2) =
    Bundle.TotalSpace.mk' E ((chartAt E p).symm ((chartAt E p) z.2))
      (mfderivWithin (𝓡 n) (𝓡 n) (chartAt E p).symm (chartAt E p).target
        ((chartAt E p) z.2) (v z.1))
  rw [mfderivWithin_of_isOpen (chartAt E p).open_target ((chartAt E p).map_source hz.2)]
  have heq := chartVectorField_at_inverse p (v z.1) ((chartAt E p) z.2)
    ((chartAt E p).map_source hz.2)
  rw [(chartAt E p).left_inv hz.2] at heq ⊢
  exact congrArg (Bundle.TotalSpace.mk' E z.2) heq




theorem pullback_chart_field_of_contDiff_one {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (p : M) {gamma : ℝ → M} {x : ℝ}
    (hgamma : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) gamma x)
    (hsource : gamma x ∈ (chartAt E p).source)
    {U : Set ℝ} (hU : IsOpen U) (hx : x ∈ U)
    (v : ℝ → E) (hv : ContDiffOn ℝ 1 v U) :
    rampHorizontalCovariantDerivative D gamma
        (fun r => chartVectorField p (v r) (gamma r)) x =
      chartVectorField p (deriv v x) (gamma x) +
        D.connection (chartVectorField p (v x)) (gamma x) (curveVelocity gamma x) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let W := fun r q => chartVectorField p (v r) q
  have hW : MDifferentiableAt ((𝓘(ℝ, ℝ)).prod (𝓡 n)) ((𝓡 n).prod (𝓡 n))
      (fun z : ℝ × M => (⟨z.2, W z.1 z.2⟩ : TangentBundle (𝓡 n) M)) (x, gamma x) :=
    ((chartVectorField_param_contMDiff_one p v U hv).contMDiffAt
      (prod_mem_nhds (hU.mem_nhds hx)
        ((chartAt E p).open_source.mem_nhds hsource))).mdifferentiableAt (by simp)
  let L := (mfderiv (𝓡 n) (𝓡 n) (chartAt E p) (gamma x)).inverse
  have htime : HasDerivAt (fun r => W r (gamma x))
      (chartVectorField p (deriv v x) (gamma x)) x :=
    L.hasFDerivAt.comp_hasDerivAt x
      (((hv x hx).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)).hasDerivAt
  have heq := (M62.hasDerivAt_fixedPointTimeDerivative W (gamma x) x hW).unique htime
  rw [M62.pullback_parametric_field D hgamma W hW, heq]

end PoincareConjecture.M63
