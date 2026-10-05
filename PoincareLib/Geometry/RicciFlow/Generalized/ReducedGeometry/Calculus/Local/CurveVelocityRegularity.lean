import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Smoothness of a manifold curve from its actual tangent velocity

The local ODE regularity argument in Morgan-Tian Definition 6.7 and
Lemma 6.8, pp. 108-109. Extended target charts convert a smooth actual
velocity into the ordinary derivative criterion. Corners in the target
do not require an open chart image.
-/

set_option autoImplicit false
-- Model tangent fibers are their given normed vector model.
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {γ : ℝ → M} {J : Set ℝ}

/-- A Ck actual tangent velocity gives a C(k+1) curve on an open
parameter set, the regularity step in Lemma 6.8, pp. 108-109. -/
theorem contMDiffOn_succ_of_curveVelocity (hJ : IsOpen J)
    (hγ : MDifferentiableOn (𝓘(ℝ, ℝ)) I γ J) (k : ℕ)
    (hV : ContMDiffOn (𝓘(ℝ, ℝ)) I.tangent k
      (fun t => Bundle.TotalSpace.mk' E (γ t)
        (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ))) J) :
    ContMDiffOn (𝓘(ℝ, ℝ)) I ((k : ℕ∞ω) + 1) γ J := by
  intro s hs
  let c := extChartAt I (γ s)
  let O := J ∩ γ ⁻¹' (chartAt H (γ s)).source
  have hO : IsOpen O := hγ.continuousOn.isOpen_inter_preimage hJ (chartAt H (γ s)).open_source
  have hsO : s ∈ O := ⟨hs, mem_chart_source H (γ s)⟩
  have hc : ContMDiffOn I (𝓘(ℝ, E)) ∞ c (chartAt H (γ s)).source := contMDiffOn_extChartAt
  have hγd (t : ℝ) (ht : t ∈ O) : MDifferentiableAt (𝓘(ℝ, ℝ)) I γ t :=
    (hγ t ht.1).mdifferentiableAt (hJ.mem_nhds ht.1)
  have hcd (t : ℝ) (ht : t ∈ O) : MDifferentiableAt I (𝓘(ℝ, E)) c (γ t) :=
    ((hc _ ht.2).contMDiffAt ((chartAt H (γ s)).open_source.mem_nhds ht.2)).mdifferentiableAt
      (by simp)
  have hcoord : DifferentiableOn ℝ (c ∘ γ) O :=
    fun t ht => ((hcd t ht).comp t (hγd t ht)).differentiableAt.differentiableWithinAt
  have htc := hc.contMDiffOn_tangentMapWithin (m := (k : ℕ∞ω))
    (by exact_mod_cast (le_top : (k : ℕ∞) + 1 ≤ ⊤))
    (chartAt H (γ s)).open_source.uniqueMDiffOn
  have hvcoord := (contMDiff_snd_tangentBundle_modelSpace E (𝓘(ℝ, E))).comp_contMDiffOn
    (htc.comp (hV.mono inter_subset_left) (fun _ ht => ht.2))
  have hderiv : ContDiffOn ℝ k (deriv (c ∘ γ)) O := by
    apply hvcoord.contDiffOn.congr
    intro t ht
    change deriv (c ∘ γ) t = mfderivWithin I (𝓘(ℝ, E)) c (chartAt H (γ s)).source (γ t)
      (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ))
    rw [mfderivWithin_of_mem_nhds ((chartAt H (γ s)).open_source.mem_nhds ht.2)]
    have hd := mfderiv_comp_apply t (hcd t ht) (hγd t ht) (1 : ℝ)
    rw [mfderiv_eq_fderiv] at hd
    change deriv (c ∘ γ) t = _ at hd
    exact hd
  have hregular : ContDiffOn ℝ ((k : ℕ∞ω) + 1) (c ∘ γ) O :=
    (contDiffOn_succ_iff_deriv_of_isOpen hO).mpr ⟨hcoord, by simp, hderiv⟩
  exact (contMDiffAt_iff_target.mpr ⟨(hγd s hsO).continuousAt,
    (hregular.contMDiffOn s hsO).contMDiffAt (hO.mem_nhds hsO)⟩).contMDiffWithinAt

/-- A differentiable solution of a jointly smooth tangent field is
smooth on its open parameter set, the interior ODE bootstrap used in
Definition 6.7 and Lemma 6.8, pp. 108-109. -/
theorem contMDiffOn_of_smooth_curveVelocity (hJ : IsOpen J)
    (hγ : MDifferentiableOn (𝓘(ℝ, ℝ)) I γ J)
    (V : ℝ → ∀ q : M, TangentSpace I q) {U : Set (ℝ × M)}
    (hV : ContMDiffOn ((𝓘(ℝ, ℝ)).prod I) I.tangent ∞
      (fun z => Bundle.TotalSpace.mk' E z.2 (V z.1 z.2)) U)
    (hgraph : ∀ t ∈ J, (t, γ t) ∈ U)
    (hderiv : ∀ t ∈ J, mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ) = V t (γ t)) :
    ContMDiffOn (𝓘(ℝ, ℝ)) I ∞ γ J := by
  rw [contMDiffOn_infty]
  intro k
  induction k with
  | zero => exact contMDiffOn_zero_iff.mpr hγ.continuousOn
  | succ k hk =>
    have hv := (hV.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl k)).comp
      (contMDiffOn_id.prodMk hk) hgraph
    have hactual : ContMDiffOn (𝓘(ℝ, ℝ)) I.tangent k
        (fun t => Bundle.TotalSpace.mk' E (γ t)
          (mfderiv (𝓘(ℝ, ℝ)) I γ t (1 : ℝ))) J := by
      apply hv.congr
      intro t ht
      simp only [Function.comp_apply, id_eq, hderiv t ht]
    exact contMDiffOn_succ_of_curveVelocity hJ hγ k hactual
