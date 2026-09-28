import PoincareConjecture.Proofs.M09.SmoothTangentChartPhase
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Calculus.Deriv.Comp

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology
open Filter

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "Q" => EuclideanSpace ℝ (Fin n)

noncomputable def inverseTangentChartPhase (p : M) (z : Q × Q) : TangentBundle (𝓡 n) M :=
  ⟨(chartAt Q p).symm z.1, (mfderiv (𝓡 n) (𝓡 n) (chartAt Q p).symm z.1) z.2⟩

set_option backward.isDefEq.respectTransparency false in
theorem inverseTangentChartPhase_contMDiffOn (p : M) :
    ContMDiffOn (𝓘(ℝ, Q × Q)) ((𝓡 n).prod (𝓡 n)) ∞
      (inverseTangentChartPhase (n := n) p) ((chartAt Q p).target ×ˢ Set.univ) := by
  have hc : ContMDiffOn (𝓡 n) (𝓡 n) ∞ (chartAt Q p).symm (chartAt Q p).target :=
    contMDiffOn_chart_symm
  have ht := hc.contMDiffOn_tangentMapWithin (m := ∞) (by simp)
    (chartAt Q p).open_target.uniqueMDiffOn
  have hmodel : ContMDiff (𝓘(ℝ, Q × Q)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun z : Q × Q ↦ (⟨z.1, z.2⟩ : TangentBundle (𝓡 n) Q)) := by
    convert! (contMDiff_tangentBundleModelSpaceHomeomorph_symm (I := 𝓡 n) (n := ∞)) using 1 <;>
      simp only [modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  have h := ht.comp hmodel.contMDiffOn
    (fun z (hz : z ∈ (chartAt Q p).target ×ˢ Set.univ) ↦ hz.1)
  apply h.congr
  intro z hz
  change (⟨(chartAt Q p).symm z.1,
      (mfderiv (𝓡 n) (𝓡 n) (chartAt Q p).symm z.1) z.2⟩ : TangentBundle (𝓡 n) M) =
    ⟨(chartAt Q p).symm z.1,
      (mfderivWithin (𝓡 n) (𝓡 n) (chartAt Q p).symm (chartAt Q p).target z.1) z.2⟩
  rw [mfderivWithin_of_isOpen (chartAt Q p).open_target hz.1]

set_option backward.isDefEq.respectTransparency false in
theorem tangentChartPhase_hasDerivAt_zero_transfer (p q : M)
    (k : ℝ → TangentBundle (𝓡 n) M) (r : ℝ) (hk : ContinuousAt k r)
    (hp : (k r).proj ∈ (chartAt Q p).source) (hq : (k r).proj ∈ (chartAt Q q).source)
    (hzero : HasDerivAt (fun u ↦ tangentChartPhase p (k u)) 0 r) :
    HasDerivAt (fun u ↦ tangentChartPhase q (k u)) 0 r := by
  let z := tangentChartPhase p (k r)
  have hz : z ∈ (chartAt Q p).target ×ˢ Set.univ :=
    ⟨(chartAt Q p).map_source hp, Set.mem_univ _⟩
  have hinv : inverseTangentChartPhase p z = k r := tangentChartPhase_inverse p (k r) hp
  have hi := (inverseTangentChartPhase_contMDiffOn p).contMDiffAt
    (((chartAt Q p).open_target.prod isOpen_univ).mem_nhds hz)
  have hsource : IsOpen {x : TangentBundle (𝓡 n) M | x.proj ∈ (chartAt Q q).source} :=
    (chartAt Q q).open_source.preimage (FiberBundle.continuous_proj Q (TangentSpace (𝓡 n)))
  have hq' : (inverseTangentChartPhase p z).proj ∈ (chartAt Q q).source := hinv ▸ hq
  have ho := (tangentChartPhase_contMDiffOn q).contMDiffAt (hsource.mem_nhds hq')
  have hd : DifferentiableAt ℝ (fun x ↦ tangentChartPhase q (inverseTangentChartPhase p x)) z :=
    (ho.comp z hi).contDiffAt.differentiableAt (by simp)
  have hcomp := hd.hasFDerivAt.comp_hasDerivAt r hzero
  simp only [map_zero] at hcomp
  have hnear : ∀ᶠ u in 𝓝 r, (k u).proj ∈ (chartAt Q p).source :=
    (((FiberBundle.continuous_proj Q (TangentSpace (𝓡 n))).continuousAt.comp hk)).preimage_mem_nhds
      ((chartAt Q p).open_source.mem_nhds hp)
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [hnear] with u hu
  change tangentChartPhase q (k u) = tangentChartPhase q
    (inverseTangentChartPhase p (tangentChartPhase p (k u)))
  rw [show inverseTangentChartPhase p (tangentChartPhase p (k u)) = k u from
    tangentChartPhase_inverse p (k u) hu]

end PoincareConjecture.Proofs.M09
