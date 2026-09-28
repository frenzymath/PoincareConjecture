import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.ModelMarkedCircles
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.StandardCriticalLevel



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

open SaddleLevel

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}



theorem exists_physical_model_morse_chart
    (d : TerminalSaddleGeometry M P p e)
    (hsize : 2 * d.r < Real.sqrt d.scale * d.matchingRadius)
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2) :
    ∃ E : OpenPartialHomeomorph E2 S2,
      closedSquare d.r ⊆ E.source ∧ 0 ∈ E.source ∧ E 0 = d.modelChart 0 ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ E E.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ E.symm E.target ∧
      E.source ⊆ e.source ∧
      (∀ x ∈ E.source, d.filledModel (E x) = g (e x)) ∧
      ∀ x ∈ E.source, inner Real (M.v : E3) (d.filledModel (E x)) =
        inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2 := by
  let k := Real.sqrt d.scale
  have hk : 0 < k := Real.sqrt_pos.mpr d.scale_pos
  let L : E2 ≃L[Real] E2 :=
    (LinearEquiv.smulOfNeZero Real E2 k⁻¹ (inv_ne_zero hk.ne')).toContinuousLinearEquiv
  let E₀ := d.modelChart.restrOpen (ball (0 : E2) d.matchingRadius) isOpen_ball
  let E := L.toHomeomorph.toOpenPartialHomeomorph.trans E₀
  have hEball (x : E2) (hx : x ∈ E.source) : L x ∈ closedBall 0 d.matchingRadius :=
    ball_subset_closedBall hx.2.2
  have hL (x : E2) : k • L x = x := by
    change k • (k⁻¹ • x) = x
    simp [smul_smul, hk.ne']
  have hEs : E.source ⊆ e.source := by
    intro x hx
    have hm := d.matching_actual_source (L x) (hEball x hx)
    change k • L x ∈ e.source at hm
    rwa [hL] at hm
  have hmatch (x : E2) (hx : x ∈ E.source) : d.filledModel (E x) = g (e x) := by
    change d.transport (d.model (d.modelChart (L x))) = g (e x)
    rw [d.matching _ (hEball x hx)]
    change g (e (k • L x)) = g (e x)
    rw [hL]
  refine ⟨E, ?_, ?_, ?_, ?_, ?_, hEs, hmatch, ?_⟩
  · intro x hx
    have hn : ‖x‖ ≤ 2 * d.r :=
      mem_closedBall_zero_iff.mp (closedSquare_subset_closedBall d.r_pos.le hx)
    have hball : L x ∈ ball (0 : E2) d.matchingRadius := by
      rw [mem_ball_zero_iff]
      change ‖k⁻¹ • x‖ < d.matchingRadius
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hk), ← div_eq_inv_mul]
      apply (div_lt_iff₀ hk).mpr
      simpa only [k, mul_comm] using hn.trans_lt hsize
    exact ⟨mem_univ _, d.matching_source (ball_subset_closedBall hball), hball⟩
  · change 0 ∈ (Set.univ : Set E2) ∧ L 0 ∈ d.modelChart.source ∩ ball 0 d.matchingRadius
    simpa only [map_zero, mem_inter_iff, mem_ball, dist_self] using
      And.intro (mem_univ (0 : E2)) ⟨d.modelChart_zero, d.matchingRadius_pos⟩
  · change d.modelChart (L 0) = d.modelChart 0
    rw [map_zero]
  · exact (d.modelChart_smooth.mono inter_subset_left).comp L.contDiff.contMDiff.contMDiffOn
      (fun _ hx => hx.2)
  · exact L.symm.contDiff.contMDiff.comp_contMDiffOn
      (d.modelChart_symm_smooth.mono (fun _ hx => hx.1.1))
  · intro x hx
    rw [hmatch x hx]
    exact hform x (hEs hx)

private theorem raw_model_central_level_facts
    (d : TerminalSaddleGeometry M P p e)
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2) :
    (∀ q : S2, d.model q 2 = d.model (d.modelChart 0) 2 →
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun y : S2 => d.model y 2) q = 0 →
        q = d.modelChart 0) ∧
      IsPreconnected {q : S2 | d.model q 2 = d.model (d.modelChart 0) 2} := by
  rcases d.model_kind with hmodel | hmodel
  · have hcenter := terminal_standard_model_chart_center d hmodel hform
    have hh : d.model (d.modelChart 0) 2 = -1 := by
      rw [hmodel, hcenter]
      exact Saddle.height_saddlePoint
    constructor
    · intro q hq hc
      rw [hh, hmodel] at hq
      change Saddle.height q = -1 at hq
      rw [hmodel] at hc
      rw [hcenter]
      exact (Saddle.critical_in_band_iff q (by rw [hq]; norm_num)).mp hc
    · rw [hh, hmodel]
      exact standard_critical_level_preconnected
  · have hc := terminal_model_chart_critical d hform
    rw [hmodel] at hc
    have hz := terminal_nested_model_chart_latitude d hmodel hform
    obtain ⟨q, hqz, hqh, hqc, _⟩ := Saddle.Nested.exists_unique_critical_point_in_height_band
    have hqp : q = d.modelChart 0 := Saddle.Nested.critical_latitude_unique_in_saddle_interval
      hqc hc (Ioo_subset_Icc_self hqz) (Ioo_subset_Icc_self hz)
    rw [hqp] at hqh
    constructor
    · intro y hy hcy
      rw [hmodel] at hy hcy
      apply (Saddle.Nested.critical_in_height_band_iff_eq_saddle hc hz y ?_).mp hcy
      change Saddle.Nested.height y = Saddle.Nested.height (d.modelChart 0) at hy
      rw [hy]
      exact ⟨hqh.1.le, by linarith [hqh.2]⟩
    · rw [hmodel]
      exact (Saddle.Nested.isConnected_critical_level_of_saddle_latitude hc hz).isPreconnected



theorem terminal_physical_model_central_level_facts
    (d : TerminalSaddleGeometry M P p e)
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2) :
    let h : S2 → Real := fun q => inner Real (M.v : E3) (d.filledModel q)
    ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h ∧
      h (d.modelChart 0) = inner Real (M.v : E3) (g p) ∧
      mfderiv (𝓡 2) 𝓘(Real, Real) h (d.modelChart 0) = 0 ∧
      (∀ q : S2, h q = h (d.modelChart 0) →
        mfderiv (𝓡 2) 𝓘(Real, Real) h q = 0 → q = d.modelChart 0) ∧
      IsPreconnected {q : S2 | h q = h (d.modelChart 0)} := by
  let h : S2 → Real := fun q => inner Real (M.v : E3) (d.filledModel q)
  let h₀ : S2 → Real := fun q => d.model q 2
  let c := inner Real (M.v : E3) (g p)
  let p₀ := d.modelChart 0
  have hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h :=
    (innerSL Real (M.v : E3)).contMDiff.comp
      (d.filledModel.contMDiff.comp (contMDiff_coe_sphere (n := 2)))
  have hh₀ : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h₀ :=
    (EuclideanSpace.proj (𝕜 := Real) (2 : Fin 3)).contMDiff.comp
      (d.model.contMDiff.comp (contMDiff_coe_sphere (n := 2)))
  have hheight (q : S2) : h q = c + d.scale * (h₀ q - h₀ p₀) := d.transport_height _
  have hcenter : h p₀ = c := by rw [hheight]; ring
  let J : Real → Real := fun y => c + d.scale * (y - h₀ p₀)
  have hJ : ContDiff Real ∞ J := by dsimp [J]; fun_prop
  have hcomp : h = J ∘ h₀ := funext hheight
  have hcritical : mfderiv (𝓡 2) 𝓘(Real, Real) h p₀ = 0 := by
    rw [hcomp, mfderiv_comp p₀ ((hJ.contMDiff _).mdifferentiableAt (by simp))
      ((hh₀ p₀).mdifferentiableAt (by simp)), terminal_model_chart_critical d hform]
    ext x
    simp
  let Jinv : Real → Real := fun y => (y - c) / d.scale + h₀ p₀
  have hJi : ContDiff Real ∞ Jinv := by dsimp [Jinv]; fun_prop
  have hraw : h₀ = Jinv ∘ h := by
    funext q
    dsimp [Jinv, comp_def]
    rw [hheight]
    field_simp [d.scale_pos.ne']
    ring
  have hcrit (q : S2) (hq : mfderiv (𝓡 2) 𝓘(Real, Real) h q = 0) :
      mfderiv (𝓡 2) 𝓘(Real, Real) h₀ q = 0 := by
    rw [hraw, mfderiv_comp q ((hJi.contMDiff _).mdifferentiableAt (by simp))
      ((hh q).mdifferentiableAt (by simp)), hq]
    ext x
    simp
  obtain ⟨hunique, hconnected⟩ := raw_model_central_level_facts d hform
  have hlevel (q : S2) : h q = h p₀ ↔ h₀ q = h₀ p₀ := by
    rw [hheight, hcenter]
    constructor <;> intro he <;> nlinarith [d.scale_pos]
  refine ⟨hh, hcenter, hcritical, ?_, ?_⟩
  · intro q hq hqc
    exact hunique q ((hlevel q).mp hq) (hcrit q hqc)
  · change IsPreconnected {q : S2 | h q = h p₀}
    have heq : {q : S2 | h q = h p₀} = {q : S2 | h₀ q = h₀ p₀} :=
      Set.ext fun q => hlevel q
    rw [heq]
    exact hconnected

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
