import PoincareConjecture.Proofs.M09.InteriorEndpointFamily
import PoincareConjecture.Proofs.M09.VelocityChainRules

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology
open Filter

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "Q" => EuclideanSpace ℝ (Fin n)

set_option backward.isDefEq.respectTransparency false in
theorem exists_smooth_interior_point_variation (α : ℝ → M) (D : Set ℝ)
    (hD : IsOpen D) (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α D)
    (L c : ℝ) (hc : c ∈ Set.Ioo 0 L) (hI : Set.Icc 0 L ⊆ D) (v : Q) :
    let e := chartAt Q (α c)
    ∃ (f : ℝ × ℝ → M) (U : Set (ℝ × ℝ)) (ρ : ℝ),
      IsOpen U ∧ 0 < ρ ∧ Set.Icc 0 L ×ˢ Set.Ioo (-ρ) ρ ⊆ U ∧
      ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (𝓡 n) ∞ f U ∧
      (∀ s ∈ Set.Icc 0 L, f (s, 0) = α s) ∧
      (∀ u, f (0, u) = α 0) ∧ (∀ u, f (L, u) = α L) ∧
      (∀ u, f (c, u) = e.symm (e (α c) + u • v)) ∧
      (curveVelocity (n := n) (fun u ↦ f (c, u)) 0 : Q) =
        mfderiv (𝓡 n) (𝓡 n) e.symm (e (α c)) v := by
  let e := chartAt Q (α c)
  let y0 := e (α c)
  let base : ℝ × ℝ → M := fun z ↦ α z.2
  have hbase : ContMDiffOn (𝓘(ℝ, ℝ × ℝ)) (𝓡 n) ∞ base (Set.univ ×ˢ D) :=
    hα.comp contDiff_snd.contMDiff.contMDiffOn (fun z hz ↦ hz.2)
  obtain ⟨Φ, Ω, N, hΩ, hN, h0N, hNΩ, hΦ, _, hleft, hright, hmark, hcenter⟩ :=
    exists_smooth_interior_endpoint_family base (Set.univ ×ˢ D)
      (isOpen_univ.prod hD) hbase 0 L c hc (fun s hs ↦ ⟨Set.mem_univ _, hI hs⟩)
  let k : ℝ × ℝ → (ℝ × Q) × ℝ := fun z ↦ ((0, y0 + z.2 • v), z.1)
  have hk : ContDiff ℝ ∞ k :=
    (contDiff_const.prodMk (contDiff_const.add (contDiff_snd.smul contDiff_const))).prodMk
      contDiff_fst
  let f : ℝ × ℝ → M := Φ ∘ k
  let U := k ⁻¹' Ω
  have hU : IsOpen U := hΩ.preimage hk.continuous
  have hf : ContMDiffOn (𝓘(ℝ, ℝ × ℝ)) (𝓡 n) ∞ f U :=
    hΦ.comp hk.contMDiff.contMDiffOn (fun _ hz ↦ hz)
  have hline : Continuous (fun u : ℝ ↦ ((0 : ℝ), y0 + u • v)) :=
    continuous_const.prodMk (continuous_const.add (continuous_id.smul continuous_const))
  have hnear : ∀ᶠ u : ℝ in 𝓝 0, ((0 : ℝ), y0 + u • v) ∈ N := by
    apply hline.continuousAt.preimage_mem_nhds
    simpa only [zero_smul, add_zero] using hN.mem_nhds h0N
  obtain ⟨ρ, hρ, hρN⟩ := Metric.mem_nhds_iff.mp hnear
  have hparam (u : ℝ) (hu : u ∈ Set.Ioo (-ρ) ρ) : ((0 : ℝ), y0 + u • v) ∈ N := by
    apply hρN
    simpa only [Real.ball_eq_Ioo, zero_sub, zero_add] using hu
  refine ⟨f, U, ρ, hU, hρ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact hNΩ ⟨hparam z.2 hz.2, hz.1⟩
  · convert! hf using 1 <;> simp only [modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  · intro s hs
    simpa only [f, Function.comp_apply, k, zero_smul, add_zero] using
      hcenter (0, y0) h0N s hs
  · intro u
    exact hleft 0 (y0 + u • v)
  · intro u
    exact hright 0 (y0 + u • v)
  · intro u
    exact hmark 0 (y0 + u • v)
  · have heq : (fun u ↦ f (c, u)) = fun u ↦ e.symm (y0 + u • v) :=
      funext (fun u ↦ hmark 0 (y0 + u • v))
    rw [heq]
    apply curveVelocity_comp_initial_line
    have hchart : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target := contMDiffOn_chart_symm
    exact (hchart.contMDiffAt
      (e.open_target.mem_nhds (e.map_source (mem_chart_source Q (α c))))).mdifferentiableAt
        (by simp)

end PoincareConjecture.Proofs.M09
