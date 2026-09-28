import PoincareConjecture.Proofs.M62.Sec19_1_PullbackConnection
import Mathlib.Analysis.Calculus.Deriv.Prod










set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

set_option backward.isDefEq.respectTransparency false in


theorem hasDerivAt_flow_metric_pairing (F : RicciFlow n M (Set.Icc a b))
    {γ : ℝ → M} {Y Z : (s : ℝ) → TangentSpace (𝓡 n) (γ s)}
    {x : ℝ} (hx : x ∈ Set.Ioo a b)
    (hγ : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) γ x)
    (hY : MDifferentiableAt (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n))
      (fun s ↦ (⟨γ s, Y s⟩ : TangentBundle (𝓡 n) M)) x)
    (hZ : MDifferentiableAt (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n))
      (fun s ↦ (⟨γ s, Z s⟩ : TangentBundle (𝓡 n) M)) x) :
    HasDerivAt (fun s ↦ (F.metric s).inner (γ s) (Y s) (Z s))
      (-2 * (F.connection x).ricci (γ x) (Y x) (Z x) +
        (F.metric x).inner (γ x)
          (rampHorizontalCovariantDerivative (F.connection x) γ Y x) (Z x) +
        (F.metric x).inner (γ x) (Y x)
          (rampHorizontalCovariantDerivative (F.connection x) γ Z x)) x := by
  let B : ℝ × ℝ → ℝ := fun z ↦ (F.metric z.1).inner (γ z.2) (Y z.2) (Z z.2)
  have hdomain : Set.Icc a b ×ˢ (Set.univ : Set M) ∈ 𝓝 (x, γ x) :=
    prod_mem_nhds (Icc_mem_nhds hx.1 hx.2) Filter.univ_mem
  have hmetric := (F.smooth.contMDiffAt hdomain).mdifferentiableAt (by simp)
  have hfst : MDifferentiableAt (𝓘(ℝ, ℝ × ℝ)) (𝓘(ℝ, ℝ))
      (Prod.fst : ℝ × ℝ → ℝ) (x, x) := differentiableAt_fst.mdifferentiableAt
  have hsnd : MDifferentiableAt (𝓘(ℝ, ℝ × ℝ)) (𝓘(ℝ, ℝ))
      (Prod.snd : ℝ × ℝ → ℝ) (x, x) := differentiableAt_snd.mdifferentiableAt
  have hgraph : MDifferentiableAt (𝓘(ℝ, ℝ × ℝ)) ((𝓘(ℝ, ℝ)).prod (𝓡 n))
      (fun z : ℝ × ℝ ↦ (z.1, γ z.2)) (x, x) :=
    hfst.prodMk (hγ.comp (x, x) hsnd)
  have hpair : MDifferentiableAt (𝓘(ℝ, ℝ × ℝ)) ((𝓡 n).prod (𝓘(ℝ, ℝ)))
      (fun z : ℝ × ℝ ↦ Bundle.TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ)
        (γ z.2) (B z)) (x, x) :=
    (hmetric.comp (x, x) hgraph).clm_bundle_apply₂
      (hY.comp (x, x) hsnd) (hZ.comp (x, x) hsnd)
  have hB : DifferentiableAt ℝ B (x, x) := by
    rw [mdifferentiableAt_totalSpace] at hpair
    exact hpair.2.differentiableAt
  have htime := (F.equation x (Set.Ioo_subset_Icc_self hx) (γ x) (Y x) (Z x)).hasDerivAt
    (Icc_mem_nhds hx.1 hx.2)
  have hspace := hasDerivAt_metric_pairing (F.connection x) hγ hY hZ
  have hfirst := hB.hasFDerivAt.comp_hasDerivAt (f := fun s : ℝ ↦ (s, x)) x
    ((hasDerivAt_id x).prodMk (hasDerivAt_const x x))
  have hsecond := hB.hasFDerivAt.comp_hasDerivAt (f := fun s : ℝ ↦ (x, s)) x
    ((hasDerivAt_const x x).prodMk (hasDerivAt_id x))
  have hdiag := hB.hasFDerivAt.comp_hasDerivAt (f := fun s : ℝ ↦ (s, s)) x
    ((hasDerivAt_id x).prodMk (hasDerivAt_id x))
  have hfirst_value : fderiv ℝ B (x, x) (1, 0) =
      -2 * (F.connection x).ricci (γ x) (Y x) (Z x) := hfirst.unique htime
  have hsecond_value : fderiv ℝ B (x, x) (0, 1) =
      (F.metric x).inner (γ x)
        (rampHorizontalCovariantDerivative (F.connection x) γ Y x) (Z x) +
      (F.metric x).inner (γ x) (Y x)
        (rampHorizontalCovariantDerivative (F.connection x) γ Z x) := hsecond.unique hspace
  apply hdiag.congr_deriv
  have hv : ((1 : ℝ), (1 : ℝ)) = (1, 0) + (0, 1) := by simp
  rw [hv, map_add, hfirst_value, hsecond_value]
  ring

end PoincareConjecture.M62
