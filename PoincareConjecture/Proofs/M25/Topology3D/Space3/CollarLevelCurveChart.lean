import PoincareConjecture.Proofs.M25.Topology3D.Space3.CollarLevelTopology
import PoincareConjecture.Proofs.M25.Topology3D.Space3.CurveOrbitCharts

set_option autoImplicit false

open Set Filter
open scoped ContDiff Manifold InnerProductSpace Topology

namespace PoincareConjecture.M25.Topology3D

theorem exists_collar_level_curve_time_chart
    (ψ : UnitTwoSphere × ℝ → E3) (hψ : IsCollarEmbedding ψ) (u : E3) (t : ℝ)
    (hreg : ∀ q : UnitTwoSphere, ⟪u, ψ (q, 0)⟫_ℝ = t →
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun p : UnitTwoSphere => ⟪u, ψ (p, 0)⟫_ℝ) q ≠ 0)
    (γ : ℝ → collarHeightLevel ψ u t) (hγ : Continuous γ)
    (hγs : ContDiff ℝ ∞ (fun r : ℝ => (γ r : E3))) (a : ℝ)
    (hγv : deriv (fun r : ℝ => (γ r : E3)) a ≠ 0) :
    ∃ k : OpenPartialHomeomorph ℝ (collarHeightLevel ψ u t), a ∈ k.source ∧
      ∀ s ∈ k.source, k s = γ s := by
  let H := collarLevelHomeomorph ψ hψ u t
  let q : ℝ → UnitTwoSphere := fun r => (H.symm (γ r)).1
  obtain ⟨ec, hec, hsrc, htgt, heci⟩ := exists_collar_chart ψ hψ
  have hγU (r : ℝ) : (γ r : E3) ∈ ec.target := by
    rw [htgt]
    obtain ⟨p, hp, heq⟩ := (γ r).2
    exact ⟨(p, 0), ⟨mem_univ _, by norm_num⟩, heq⟩
  have hqeq : q = fun r => (ec.symm (γ r : E3)).1 :=
    funext fun r => collarLevelHomeomorph_symm_eq ψ hψ u t ec hec hsrc (γ r)
  have hqs : ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ∞ q := by
    rw [hqeq]
    apply contMDiffOn_univ.mp
    have hi : ContMDiffOn 𝓘(ℝ, E3) (𝓡 2) ∞ (fun z => (ec.symm z).1) ec.target :=
      contMDiff_fst.comp_contMDiffOn heci
    exact hi.comp hγs.contMDiff.contMDiffOn (fun r _ => hγU r)
  let f : UnitTwoSphere → ℝ := fun p => ⟪u, ψ (p, 0)⟫_ℝ
  have hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f :=
    (InnerProductSpace.toDual ℝ E3 u).contDiff.contMDiff.comp
      (collar_central_contMDiff ψ hψ)
  have hqt (r : ℝ) : f (q r) = t := (H.symm (γ r)).2
  obtain ⟨c, hca, hcs, hci, hcoord⟩ :=
    exists_surface_regular_chart (E := E2) (by simp [E2]) f hf (q a)
      (hreg (q a) (hqt a))
  let l := levelSliceChart f t c hcoord (H.symm (γ a))
  let e := H.symm.toOpenPartialHomeomorph.trans l
  have hesrc (r : ℝ) : γ r ∈ e.source ↔ q r ∈ c.source := by
    change ((γ r ∈ univ) ∧ q r ∈ c.source) ↔ q r ∈ c.source
    simp only [mem_univ, true_and]
  have hea : γ a ∈ e.source := (hesrc a).mpr hca
  let η : ℝ → ℝ := fun r => e (γ r)
  have hηeq (r : ℝ) : η r = (c (q r)).1 := rfl
  have hη : ContDiffOn ℝ ∞ η (γ ⁻¹' e.source) := by
    change ContDiffOn ℝ ∞ (fun r => (c (q r)).1) (γ ⁻¹' e.source)
    exact (contDiff_fst.contMDiff.comp_contMDiffOn
      (hcs.comp hqs.contMDiffOn (fun r hr => (hesrc r).mp hr))).contDiffOn
  have hpair (r : ℝ) (hr : γ r ∈ e.source) : (η r, t) = c (q r) :=
    Prod.ext (hηeq r) ((hcoord (q r) ((hesrc r).mp hr)).trans (hqt r)).symm
  let G : ℝ × ℝ → E3 := fun v => ψ (c.symm v, 0)
  have hG : ContDiffOn ℝ ∞ G c.target :=
    ((collar_central_contMDiff ψ hψ).comp_contMDiffOn hci).contDiffOn
  have hGa : (η a, t) ∈ c.target := by
    rw [hpair a hea]
    exact c.map_source hca
  have hnear : (fun r => G (η r, t)) =ᶠ[𝓝 a] (fun r => (γ r : E3)) := by
    filter_upwards [hγ.continuousAt.preimage_mem_nhds (e.open_source.mem_nhds hea)] with r hr
    change ψ (c.symm (η r, t), 0) = (γ r : E3)
    rw [hpair r hr, c.left_inv ((hesrc r).mp hr)]
    exact congrArg Subtype.val (H.apply_symm_apply (γ r))
  have hηv : deriv η a ≠ 0 := by
    intro hz
    have hdη := ((hη.contDiffAt ((e.open_source.preimage hγ).mem_nhds hea)).differentiableAt
      (by simp)).hasDerivAt
    have hdG := ((hG.contDiffAt (c.open_target.mem_nhds hGa)).differentiableAt
      (by simp)).hasFDerivAt.comp_hasDerivAt a (hdη.prodMk (hasDerivAt_const a t))
    have hzero : deriv (fun r => G (η r, t)) a = 0 := by
      simpa only [Function.comp_def, hz, Prod.mk_zero_zero, map_zero] using hdG.deriv
    exact hγv (hnear.deriv_eq.symm.trans hzero)
  exact exists_curve_time_chart γ hγ e a hea hη hηv

end PoincareConjecture.M25.Topology3D
