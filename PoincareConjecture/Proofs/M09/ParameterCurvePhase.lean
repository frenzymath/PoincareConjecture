import PoincareConjecture.Proofs.M09.FamilyPhase
import PoincareConjecture.Proofs.M09.TangentChartPhase
import PoincareConjecture.Proofs.M09.ChartVelocity
import PoincareConjecture.Proofs.M09.SmoothPartials

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "Q" => EuclideanSpace ℝ (Fin n)

noncomputable def parameterCurvePhase (H : ℝ × ℝ → M) (z : ℝ × ℝ) : TangentBundle (𝓡 n) M :=
  curvePhase (n := n) (fun s ↦ H (s, z.2)) z.1

set_option backward.isDefEq.respectTransparency false in
theorem parameterCurvePhase_contMDiffOn (H : ℝ × ℝ → M) (U : Set (ℝ × ℝ))
    (hU : IsOpen U) (hH : ContMDiffOn (𝓘(ℝ, ℝ × ℝ)) (𝓡 n) ∞ H U) :
    ContMDiffOn (𝓘(ℝ, ℝ × ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (parameterCurvePhase (n := n) H) U := by
  have hswap : ContDiff ℝ ∞ (Prod.swap : ℝ × ℝ → ℝ × ℝ) :=
    contDiff_snd.prodMk contDiff_fst
  have hHU : ContMDiffOn (𝓘(ℝ, ℝ × ℝ)) (𝓡 n) ∞ (H ∘ Prod.swap) (Prod.swap ⁻¹' U) :=
    hH.comp hswap.contMDiff.contMDiffOn (fun _ hz ↦ hz)
  have hphase := familyPhase_contMDiffOn (H ∘ Prod.swap) (Prod.swap ⁻¹' U)
    (hU.preimage hswap.continuous) hHU
  exact hphase.comp hswap.contMDiff.contMDiffOn (fun _ hz ↦ hz)

theorem tangentChartPhase_parameter_eq (H : ℝ × ℝ → M) (U : Set (ℝ × ℝ))
    (hU : IsOpen U) (hH : ContMDiffOn (𝓘(ℝ, ℝ × ℝ)) (𝓡 n) ∞ H U)
    (p : M) (z : ℝ × ℝ) (hz : z ∈ U) (hp : H z ∈ (chartAt Q p).source) :
    tangentChartPhase p (parameterCurvePhase (n := n) H z) =
      timeDerivativePhase (fun w ↦ (chartAt Q p) (H w)) z := by
  have hslice : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) (fun s ↦ H (s, z.2)) z.1 :=
    ((hH.contMDiffAt (hU.mem_nhds hz)).comp z.1
      (contDiff_id.prodMk contDiff_const).contMDiff.contMDiffAt).mdifferentiableAt (by simp)
  apply Prod.ext
  · rfl
  · exact (hasDerivAt_chart_curve p (fun s ↦ H (s, z.2)) z.1 hp hslice).deriv.symm

theorem tangentChartPhase_parameter_contDiffOn (H : ℝ × ℝ → M) (U : Set (ℝ × ℝ))
    (hU : IsOpen U) (hH : ContMDiffOn (𝓘(ℝ, ℝ × ℝ)) (𝓡 n) ∞ H U) (p : M) :
    ContDiffOn ℝ ∞ (fun z ↦ tangentChartPhase p (parameterCurvePhase (n := n) H z))
      (U ∩ H ⁻¹' (chartAt Q p).source) := by
  let Ω := U ∩ H ⁻¹' (chartAt Q p).source
  have hΩ : IsOpen Ω := hH.continuousOn.isOpen_inter_preimage hU (chartAt Q p).open_source
  have hc : ContDiffOn ℝ ∞ (fun z ↦ (chartAt Q p) (H z)) Ω :=
    (contMDiffOn_chart.comp (hH.mono Set.inter_subset_left) (fun _ hz ↦ hz.2)).contDiffOn
  apply (timeDerivativePhase_contDiffOn _ Ω hΩ hc).congr
  intro z hz
  exact tangentChartPhase_parameter_eq H U hU hH p z hz.1 hz.2

end PoincareConjecture.Proofs.M09
