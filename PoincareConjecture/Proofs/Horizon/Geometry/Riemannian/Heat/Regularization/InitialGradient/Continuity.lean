import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Gradient.SpaceTime
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Coefficients

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology
open Bundle Filter Set

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

private lemma gradient_normSq_eq_chart (D : LeviCivitaData g)
    {f : M → ℝ} {x : M} {z : EuclideanSpace ℝ (Fin n)}
    (hz : z ∈ (extChartAt (𝓡 n) x).target)
    (hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f ((extChartAt (𝓡 n) x).symm z)) :
    let y := (extChartAt (𝓡 n) x).symm z
    let d := fderiv ℝ (f ∘ (extChartAt (𝓡 n) x).symm) z
    let B := g.pullbackCoefficients (extChartAt (𝓡 n) x).symm z
    g.inner y (D.gradient f y) (D.gradient f y) = d (B.inverse d) := by
  let e := extChartAt (𝓡 n) x
  let y := e.symm z
  let A := mfderiv (𝓡 n) (𝓡 n) e.symm z
  let d := fderiv ℝ (f ∘ e.symm) z
  let B := g.pullbackCoefficients e.symm z
  have hA : A.IsInvertible := by
    simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
      isInvertible_mfderivWithin_extChartAt_symm (I := 𝓡 n) hz
  have hB : B.IsInvertible := g.isInvertible_chartCoefficients x hz
  have hd : d = (mvfderiv (𝓡 n) f y).comp A := by
    have hi := (mdifferentiableWithinAt_extChartAt_symm (I := 𝓡 n) hz)
    simp only [ModelWithCorners.range_eq_univ, mdifferentiableWithinAt_univ] at hi
    have hh := mfderiv_comp z hf hi
    rw [mfderiv_eq_fderiv] at hh
    exact hh
  have hBA : B (A.inverse (D.gradient f y)) = d := by
    ext v
    change g.inner (e.symm z) (A (A.inverse (D.gradient f y))) (A v) = d v
    rw [hA.self_apply_inverse, D.inner_gradient, hd]
    rfl
  change g.inner y (D.gradient f y) (D.gradient f y) = d (B.inverse d)
  rw [hB.inverse_apply_eq.mpr hBA.symm, hd]
  simp only [ContinuousLinearMap.comp_apply, D.inner_gradient]
  exact congrArg (mvfderiv (𝓡 n) f y) (hA.self_apply_inverse (D.gradient f y)).symm

theorem tendsto_gradient_normSq_of_initial_chart_derivative (D : LeviCivitaData g)
    {F : ℝ × M → ℝ} {f : M → ℝ} {x : M}
    (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ F (Ioi 0 ×ˢ univ))
    (hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f x)
    (htrace : Tendsto
      (fun p : ℝ × M => fderiv ℝ
        (fun z => F (p.1, (extChartAt (𝓡 n) x).symm z))
        (extChartAt (𝓡 n) x p.2))
      (𝓝[Ioi 0 ×ˢ univ] (0, x))
      (𝓝 (fderiv ℝ (f ∘ (extChartAt (𝓡 n) x).symm) (extChartAt (𝓡 n) x x)))) :
    Tendsto
      (fun p : ℝ × M => g.inner p.2 (D.gradient (fun y => F (p.1, y)) p.2)
        (D.gradient (fun y => F (p.1, y)) p.2))
      (𝓝[Ioi 0 ×ˢ univ] (0, x))
      (𝓝 (g.inner x (D.gradient f x) (D.gradient f x))) := by
  let e := extChartAt (𝓡 n) x
  let B := g.pullbackCoefficients e.symm
  let d := fun p : ℝ × M => fderiv ℝ (fun z => F (p.1, e.symm z)) (e p.2)
  let d₀ := fderiv ℝ (f ∘ e.symm) (e x)
  have hB : ContinuousAt B (e x) :=
    (g.contDiffOn_chartCoefficients x).continuousOn.continuousAt
      ((isOpen_extChartAt_target (I := 𝓡 n) x).mem_nhds (mem_extChartAt_target x))
  have hi := (g.isInvertible_chartCoefficients x (mem_extChartAt_target x)).contDiffAt_map_inverse
    (n := ∞)
  have hc : ContinuousAt (fun p : ℝ × M => e p.2) (0, x) :=
    (continuousAt_extChartAt (I := 𝓡 n) x).comp continuousAt_snd
  have hBp : ContinuousAt (fun p : ℝ × M => B (e p.2)) (0, x) :=
    hB.tendsto.comp hc.tendsto
  have hBc : ContinuousAt (fun p : ℝ × M => (B (e p.2)).inverse) (0, x) :=
    hi.continuousAt.tendsto.comp hBp.tendsto
  have hBi : Tendsto (fun p : ℝ × M => (B (e p.2)).inverse)
      (𝓝[Ioi 0 ×ˢ univ] (0, x)) (𝓝 (B (e x)).inverse) :=
    hBc.tendsto.mono_left nhdsWithin_le_nhds
  have hv := ((isBoundedBilinearMap_apply (𝕜 := ℝ)).continuous.tendsto _).comp
    (hBi.prodMk_nhds htrace)
  have hlim := ((isBoundedBilinearMap_apply (𝕜 := ℝ)).continuous.tendsto _).comp
    (htrace.prodMk_nhds hv)
  have hzero : g.inner x (D.gradient f x) (D.gradient f x) = d₀ ((B (e x)).inverse d₀) := by
    have hf' : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f (e.symm (e x)) := by
      simpa only [e, extChartAt_to_inv] using hf
    have hh := gradient_normSq_eq_chart D (mem_extChartAt_target x) hf'
    change g.inner (e.symm (e x)) (D.gradient f (e.symm (e x)))
      (D.gradient f (e.symm (e x))) = d₀ ((B (e x)).inverse d₀) at hh
    rwa [e.left_inv (mem_extChartAt_source x)] at hh
  rw [hzero]
  apply hlim.congr'
  have hnear : ∀ᶠ p : ℝ × M in 𝓝[Ioi 0 ×ˢ univ] (0, x), p.2 ∈ e.source :=
    (continuousAt_snd.tendsto.mono_left nhdsWithin_le_nhds).eventually
      (extChartAt_source_mem_nhds (I := 𝓡 n) x)
  filter_upwards [hnear, self_mem_nhdsWithin] with p hp ht
  have hFp := hF.contMDiffAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds ht)
  have hslice : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) (fun y => F (p.1, y)) p.2 :=
    (hFp.comp p.2 (contMDiffAt_const.prodMk contMDiffAt_id)).mdifferentiableAt (by simp)
  have hslicee : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ)
      (fun y => F (p.1, y)) (e.symm (e p.2)) := by
    simpa only [e.left_inv hp] using hslice
  have hh := gradient_normSq_eq_chart D (e.map_source hp) hslicee
  change g.inner (e.symm (e p.2)) (D.gradient (fun y => F (p.1, y)) (e.symm (e p.2)))
    (D.gradient (fun y => F (p.1, y)) (e.symm (e p.2))) =
      d p ((B (e p.2)).inverse (d p)) at hh
  rw [e.left_inv hp] at hh
  exact hh.symm

theorem continuousOn_gradient_normSq_of_initial_chart_derivative (D : LeviCivitaData g)
    {F : ℝ × M → ℝ} {f : M → ℝ}
    (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ F (Ioi 0 ×ˢ univ))
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hzero : ∀ x, F (0, x) = f x)
    (htrace : ∀ x, Tendsto
      (fun p : ℝ × M => fderiv ℝ
        (fun z => F (p.1, (extChartAt (𝓡 n) x).symm z))
        (extChartAt (𝓡 n) x p.2))
      (𝓝[Ioi 0 ×ˢ univ] (0, x))
      (𝓝 (fderiv ℝ (f ∘ (extChartAt (𝓡 n) x).symm) (extChartAt (𝓡 n) x x)))) :
    ContinuousOn
      (fun p : ℝ × M => g.inner p.2 (D.gradient (fun y => F (p.1, y)) p.2)
        (D.gradient (fun y => F (p.1, y)) p.2)) (Ici 0 ×ˢ univ) := by
  have hzero' : (fun y => F (0, y)) = f := funext hzero
  rintro ⟨t, x⟩ hp
  by_cases ht : 0 < t
  · have hFp := hF.contMDiffAt (x := (t, x))
      ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨ht, mem_univ x⟩)
    exact (D.contMDiffAt_gradient_normSq_spacetime hFp).continuousAt.continuousWithinAt
  · have ht0 : t = 0 := le_antisymm (le_of_not_gt ht) hp.1
    subst t
    have hpos : ContinuousWithinAt
        (fun p : ℝ × M => g.inner p.2 (D.gradient (fun y => F (p.1, y)) p.2)
          (D.gradient (fun y => F (p.1, y)) p.2)) (Ioi 0 ×ˢ univ) (0, x) := by
      simpa only [ContinuousWithinAt, hzero'] using
        D.tendsto_gradient_normSq_of_initial_chart_derivative hF
          ((hf x).mdifferentiableAt (by simp)) (htrace x)
    have hi := D.contMDiffAt_gradient_normSq_spacetime
      ((hf x).comp (0, x) (contMDiffAt_snd (I := 𝓘(ℝ, ℝ))))
    have hboundary : ContinuousWithinAt
        (fun p : ℝ × M => g.inner p.2 (D.gradient (fun y => F (p.1, y)) p.2)
          (D.gradient (fun y => F (p.1, y)) p.2)) ({0} ×ˢ univ) (0, x) := by
      apply hi.continuousAt.continuousWithinAt.congr
      · rintro ⟨s, y⟩ hs
        have hs0 : s = 0 := hs.1
        simp only [hs0, hzero', Function.comp_apply]
      · simp only [hzero', Function.comp_apply]
    have hs : (Ici (0 : ℝ) ×ˢ (univ : Set M)) =
        (Ioi 0 ×ˢ univ) ∪ ({0} ×ˢ univ) := by
      ext p
      simp only [mem_prod, mem_Ici, mem_univ, and_true, mem_union, mem_Ioi,
        mem_singleton_iff]
      exact le_iff_lt_or_eq.trans (by rw [eq_comm])
    rw [hs]
    exact hpos.union hboundary

end PoincareConjecture.LeviCivitaData
