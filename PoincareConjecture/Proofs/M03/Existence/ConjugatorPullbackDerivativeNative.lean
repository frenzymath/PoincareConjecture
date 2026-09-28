import PoincareConjecture.Proofs.M03.Existence.ConjugatorChartLieNative
import PoincareConjecture.Proofs.M03.Existence.ConjugatorWithinDerivativeNative
import Mathlib.Geometry.Manifold.Diffeomorph

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology

noncomputable section

universe u

namespace PoincareConjecture.ConjugatorLieDerivativeNative

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

theorem chartMap_spatial_derivative
    (Φ : Diffeomorph (𝓡 n) (𝓡 n) M M ∞) (p q : M) {x : M}
    (hp : x ∈ (chartAt E p).source) (hq : Φ x ∈ (chartAt E q).source)
    (u : TangentSpace (𝓡 n) x) :
    fderiv ℝ (fun z => chartAt E q (Φ ((chartAt E p).symm z)))
        (chartAt E p x) (mfderiv (𝓡 n) 𝓘(ℝ, E) (chartAt E p) x u) =
      mfderiv (𝓡 n) 𝓘(ℝ, E) (chartAt E q) (Φ x)
        (mfderiv (𝓡 n) (𝓡 n) Φ x u) := by
  have hback := (chartAt E p).left_inv hp
  have hi := (mdifferentiable_chart (I := 𝓡 n) p).mdifferentiableAt_symm
    ((chartAt E p).map_source hp)
  have hPhi := Φ.mdifferentiable (by simp) x
  have hiPhi : MDifferentiableAt 𝓘(ℝ, E) (𝓡 n)
      (Φ ∘ (chartAt E p).symm) (chartAt E p x) := by
    exact hPhi.comp_of_eq (chartAt E p x) hi hback
  have houter := mfderiv_comp_apply_of_eq (chartAt E p x)
    ((mdifferentiable_chart (I := 𝓡 n) q).mdifferentiableAt hq) hiPhi
    (show (Φ ∘ (chartAt E p).symm) (chartAt E p x) = Φ x by simp only [Function.comp_apply, hback])
    (mfderiv (𝓡 n) 𝓘(ℝ, E) (chartAt E p) x u)
  have hinner := mfderiv_comp_apply_of_eq (chartAt E p x) hPhi hi hback
    (mfderiv (𝓡 n) 𝓘(ℝ, E) (chartAt E p) x u)
  have hinv := congrArg (fun L : TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x => L u)
    ((mdifferentiable_chart (I := 𝓡 n) p).symm_comp_deriv hp)
  have hinv' :
      mfderiv 𝓘(ℝ, E) (𝓡 n) (chartAt E p).symm (chartAt E p x)
        (mfderiv (𝓡 n) 𝓘(ℝ, E) (chartAt E p) x u) = u := hinv
  rw [hinv'] at hinner
  rw [hinner, mfderiv_eq_fderiv] at houter
  exact houter

theorem chartMetricForm_chartMap
    (g : RiemannianMetric n M) (Φ : Diffeomorph (𝓡 n) (𝓡 n) M M ∞)
    (p q : M) {x : M} (hp : x ∈ (chartAt E p).source)
    (hq : Φ x ∈ (chartAt E q).source) (u v : TangentSpace (𝓡 n) x) :
    chartMetricForm g q (chartAt E q (Φ x))
        (fderiv ℝ (fun z => chartAt E q (Φ ((chartAt E p).symm z)))
          (chartAt E p x) (mfderiv (𝓡 n) 𝓘(ℝ, E) (chartAt E p) x u))
        (fderiv ℝ (fun z => chartAt E q (Φ ((chartAt E p).symm z)))
          (chartAt E p x) (mfderiv (𝓡 n) 𝓘(ℝ, E) (chartAt E p) x v)) =
      g.inner (Φ x) (mfderiv (𝓡 n) (𝓡 n) Φ x u) (mfderiv (𝓡 n) (𝓡 n) Φ x v) := by
  rw [chartMetricForm_apply, (chartAt E q).left_inv hq,
    chartMap_spatial_derivative Φ p q hp hq u,
    chartMap_spatial_derivative Φ p q hp hq v]
  have hinv := (mdifferentiable_chart (I := 𝓡 n) q).symm_comp_deriv hq
  have hu := congrArg (fun L : TangentSpace (𝓡 n) (Φ x) →L[ℝ]
      TangentSpace (𝓡 n) (Φ x) => L (mfderiv (𝓡 n) (𝓡 n) Φ x u)) hinv
  have hv := congrArg (fun L : TangentSpace (𝓡 n) (Φ x) →L[ℝ]
      TangentSpace (𝓡 n) (Φ x) => L (mfderiv (𝓡 n) (𝓡 n) Φ x v)) hinv
  exact congrArg₂ (fun a b => g.inner (Φ x) a b) hu hv

theorem hasDerivWithinAt_fixedMetric_pullback_neg
    {T t : ℝ} (hT : 0 < T) (ht : t ∈ Set.Ico 0 T)
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    (Φ : ℝ → Diffeomorph (𝓡 n) (𝓡 n) M M ∞)
    (W : (y : M) → TangentSpace (𝓡 n) y)
    (hΦ : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞
      (fun q : ℝ × M => Φ q.1 q.2) (Set.Ico 0 T ×ˢ Set.univ))
    (hW : ∀ y, ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞ (T% W) y)
    (hgen : ∀ y : M, HasMFDerivWithinAt 𝓘(ℝ, ℝ) (𝓡 n)
      (fun s => Φ s y) (Set.Ico 0 T) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (-W (Φ t y))))
    (x : M) (u v : TangentSpace (𝓡 n) x) :
    HasDerivWithinAt
      (fun s => g.inner (Φ s x)
        (mfderiv (𝓡 n) (𝓡 n) (Φ s) x u)
        (mfderiv (𝓡 n) (𝓡 n) (Φ s) x v))
      (-DeTurckNative.metricLieDerivative D W (Φ t x)
        (mfderiv (𝓡 n) (𝓡 n) (Φ t) x u)
        (mfderiv (𝓡 n) (𝓡 n) (Φ t) x v)) (Set.Ico 0 T) t := by
  let p := x
  let q := Φ t x
  let z₀ := chartAt E p x
  let F : ℝ × E → E := fun a => chartAt E q (Φ a.1 ((chartAt E p).symm a.2))
  let U := (chartAt E p).target
  let J := Set.Ico 0 T
  let V : E → E := fun z => -chartVector q W z
  have hp : x ∈ (chartAt E p).source := mem_chart_source E x
  have hq : Φ t x ∈ (chartAt E q).source := mem_chart_source E (Φ t x)
  have hz₀ : z₀ ∈ U := (chartAt E p).map_source hp
  have hback : (chartAt E p).symm z₀ = x := (chartAt E p).left_inv hp
  have hFval : F (t, z₀) = chartAt E q (Φ t x) := by simp only [F, hback]
  have hFtgt : F (t, z₀) ∈ (chartAt E q).target := by
    rw [hFval]
    exact (chartAt E q).map_source hq
  have hFback : (chartAt E q).symm (F (t, z₀)) = Φ t x := by
    rw [hFval, (chartAt E q).left_inv hq]
  have hcoord : ContDiffWithinAt ℝ 2 F (J ×ˢ U) (t, z₀) := by
    have hinverse : ContMDiffWithinAt 𝓘(ℝ, E) (𝓡 n) ∞
        (chartAt E p).symm U z₀ := contMDiffOn_chart_symm (I := 𝓡 n) (x := p) z₀ hz₀
    have hparam : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E))
        (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
        (fun a : ℝ × E => (a.1, (chartAt E p).symm a.2)) (J ×ˢ U) (t, z₀) := by
      exact contMDiffWithinAt_fst.prodMk
        (hinverse.comp (t, z₀) contMDiffWithinAt_snd (fun _ ha => ha.2))
    have hflow := (hΦ (t, x) ⟨ht, Set.mem_univ x⟩).comp_of_eq hparam
      (fun _ ha => ⟨ha.1, Set.mem_univ _⟩) (by simp only [hback])
    have hchart : ContMDiffAt (𝓡 n) 𝓘(ℝ, E) ∞ (chartAt E q) (Φ t x) :=
      (contMDiffOn_chart (I := 𝓡 n) (x := q) (Φ t x) hq).contMDiffAt
        ((chartAt E q).open_source.mem_nhds hq)
    have hc := hchart.comp_contMDiffWithinAt_of_eq hflow
      (by simp only [Function.comp_apply, hback])
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hc
    exact hc.contDiffWithinAt.of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have hV : DifferentiableAt ℝ V (F (t, z₀)) := by
    have h := (chartVector_contDiffAt q hFtgt (by rw [hFback]; exact hW _)).differentiableAt (by simp)
    exact h.neg
  have hG : DifferentiableAt ℝ (chartMetricForm g q) (F (t, z₀)) :=
    ((chartMetricForm_contDiffOn g q).contDiffAt
      ((chartAt E q).open_target.mem_nhds hFtgt)).differentiableAt (by simp)
  have htarget : ∀ᶠ z in 𝓝 z₀,
      Φ t ((chartAt E p).symm z) ∈ (chartAt E q).source := by
    have hc : ContinuousAt (fun z => Φ t ((chartAt E p).symm z)) z₀ :=
      (Φ t).continuous.continuousAt.comp
        ((chartAt E p).continuousOn_symm.continuousAt ((chartAt E p).open_target.mem_nhds hz₀))
    exact hc (by simpa only [hback] using (chartAt E q).open_source.mem_nhds hq)
  have horbit : ∀ᶠ z in 𝓝 z₀,
      HasDerivWithinAt (fun s => F (s, z)) (V (F (t, z))) J t := by
    filter_upwards [htarget] with z hz
    have hc := HasMFDerivAt.comp_hasMFDerivWithinAt t
      (f := fun s => Φ s ((chartAt E p).symm z))
      ((mdifferentiable_chart (I := 𝓡 n) q).mdifferentiableAt hz).hasMFDerivAt
      (hgen ((chartAt E p).symm z))
    have hd := hc.hasFDerivWithinAt.hasDerivWithinAt
    have hv : V (F (t, z)) =
        -mfderiv (𝓡 n) 𝓘(ℝ, E) (chartAt E q) (Φ t ((chartAt E p).symm z))
          (W (Φ t ((chartAt E p).symm z))) := by
      dsimp only [V, F]
      rw [chartVector_chart q W hz]
    rw [hv]
    have hraw : HasDerivWithinAt (fun s => F (s, z))
        (mfderiv (𝓡 n) 𝓘(ℝ, E) (chartAt E q) (Φ t ((chartAt E p).symm z))
          ((1 : ℝ) • (-W (Φ t ((chartAt E p).symm z))))) J t := hd
    simpa only [one_smul, map_neg] using hraw
  let cu := mfderiv (𝓡 n) 𝓘(ℝ, E) (chartAt E p) x u
  let cv := mfderiv (𝓡 n) 𝓘(ℝ, E) (chartAt E p) x v
  have hcalc := hasDerivWithinAt_pullback_coefficient_of_contDiffWithinAt
    (chartAt E p).open_target (uniqueDiffOn_Ico 0 T) ht hz₀
    (mem_closure_interior_Ico_prod (chartAt E p).open_target hT ht hz₀)
    hcoord hV hG horbit cu cv
  have htimeTarget : ∀ᶠ s in 𝓝[J] t, Φ s x ∈ (chartAt E q).source := by
    exact (hgen x).continuousWithinAt ((chartAt E q).open_source.mem_nhds hq)
  have heq :
      (fun s => g.inner (Φ s x)
        (mfderiv (𝓡 n) (𝓡 n) (Φ s) x u)
        (mfderiv (𝓡 n) (𝓡 n) (Φ s) x v)) =ᶠ[𝓝[J] t]
      (fun s => chartMetricForm g q (F (s, z₀))
        (fderiv ℝ (fun z => F (s, z)) z₀ cu)
        (fderiv ℝ (fun z => F (s, z)) z₀ cv)) := by
    filter_upwards [htimeTarget] with s hs
    simpa only [F, hback] using (chartMetricForm_chartMap g (Φ s) p q hp hs u v).symm
  have htransport := hcalc.congr_of_eventuallyEq_of_mem heq ht
  apply htransport.congr_deriv
  rw [coordinateLieMetric_neg]
  congr 1
  rw [coordinateLieMetric_chart_eq D q hFtgt (by rw [hFback]; exact hW _), hFback]
  have hu := chartMap_spatial_derivative (Φ t) p q hp hq u
  have hv := chartMap_spatial_derivative (Φ t) p q hp hq v
  change fderiv ℝ (fun z => F (t, z)) z₀ cu = _ at hu
  change fderiv ℝ (fun z => F (t, z)) z₀ cv = _ at hv
  rw [hu, hv, hFval]
  have hinv := (mdifferentiable_chart (I := 𝓡 n) q).symm_comp_deriv hq
  exact congrArg₂ (fun a b => DeTurckNative.metricLieDerivative D W (Φ t x) a b)
    (congrArg (fun L : TangentSpace (𝓡 n) (Φ t x) →L[ℝ]
      TangentSpace (𝓡 n) (Φ t x) => L (mfderiv (𝓡 n) (𝓡 n) (Φ t) x u)) hinv)
    (congrArg (fun L : TangentSpace (𝓡 n) (Φ t x) →L[ℝ]
      TangentSpace (𝓡 n) (Φ t x) => L (mfderiv (𝓡 n) (𝓡 n) (Φ t) x v)) hinv)

end PoincareConjecture.ConjugatorLieDerivativeNative

end
