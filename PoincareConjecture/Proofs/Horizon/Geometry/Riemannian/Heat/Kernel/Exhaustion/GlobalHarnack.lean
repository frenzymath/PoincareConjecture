import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.LiYau.DomainDistanceBound
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.LiYau.Path
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.LiYau.Geodesic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Exhaustion.Bounded
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Exhaustion.Supremum

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology Bundle ENNReal

universe u

namespace PoincareConjecture.LeviCivitaData

private lemma edist_self_for_global_harnack
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (x : M) : g.edist x x = 0 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  simp only [RiemannianMetric.edist, Manifold.riemannianEDist_self]

theorem dirichletExhaustionKernel_global_harnack_of_ricci_lower
    {m : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
    [IsManifold (𝓡 (m + 1)) ∞ M] [PreconnectedSpace M]
    {g : RiemannianMetric (m + 1) M} (D : LeviCivitaData g)
    (hm : 0 < m) (hc : MetricComplete g) {κ : ℝ} (hκ : 0 ≤ κ)
    (hRic : ∀ x (v : TangentSpace (𝓡 (m + 1)) x),
      -(m : ℝ) * κ * g.inner x v v ≤ D.ricci x v v)
    {Ω : ℕ → Set M} (hΩ : ∀ j, IsOpen (Ω j)) (hΩmono : Monotone Ω)
    (hcover : (⋃ j, Ω j) = univ) {K : ℕ → ℝ → M → M → ℝ}
    (hK : ∀ j, Dirichlet.IsDirichletHeatKernel D (Ω j) (K j))
    (hmono : ∀ t, 0 < t → ∀ x y, Monotone (fun j => K j t x y))
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (x z y : M) :
    dirichletExhaustionKernel K a x y ≤
      dirichletExhaustionKernel K b z y * Real.exp
        (2 * ((m + 1 : ℕ) : ℝ) * Real.log (b / a) +
          2 * ((m + 1 : ℕ) : ℝ) * ((m : ℝ) * κ) * (b - a) +
          (g.edist x z).toReal ^ 2 / (2 * (b - a))) := by
  obtain ⟨e, he, hlocal⟩ := D.exists_liYau_radius_error_on_domains hm hc hκ hRic
  have hbdd : ∀ t, 0 < t → ∀ p q, BddAbove (range (fun j => K j t p q)) :=
    fun t ht p q => by
      apply D.bddAbove_dirichletHeatKernel_exhaustion
        (by omega) hc (k := (m : ℝ) * κ) (by positivity)
        (fun q v => by simpa [mul_assoc] using hRic q v)
        hΩ hΩmono hcover hK hmono ht p q
  let E₀ := Real.exp (2 * ((m + 1 : ℕ) : ℝ) * Real.log (b / a) +
    2 * ((m + 1 : ℕ) : ℝ) * ((m : ℝ) * κ) * (b - a) +
    (g.edist x z).toReal ^ 2 / (2 * (b - a)))
  have hfinite : ∀ R : ℝ, 1 ≤ R → (g.edist x z).toReal ≤ R →
      dirichletExhaustionKernel K a x y ≤
        dirichletExhaustionKernel K b z y *
          Real.exp (2 * ((m + 1 : ℕ) : ℝ) * Real.log (b / a) +
            2 * ((m + 1 : ℕ) : ℝ) * ((m : ℝ) * κ) * (b - a) +
            2 * ((m + 1 : ℕ) : ℝ) * e (3 * R) * (b - a) +
            (g.edist x z).toReal ^ 2 / (2 * (b - a))) := by
    intro R hR hdist
    have hxx0 : g.edist x x = 0 := edist_self_for_global_harnack g x
    have hxx : (g.edist x x).toReal = 0 := by rw [hxx0, ENNReal.toReal_zero]
    have hball := g.isCompact_closedBall_of_metricComplete hc x (6 * R)
    obtain ⟨N, hN⟩ := hball.elim_directed_cover Ω hΩ (by rw [hcover]; exact subset_univ _)
      (fun i j => ⟨max i j, hΩmono (le_max_left _ _), hΩmono (le_max_right _ _)⟩)
    have hcontains : {p | (g.edist x p).toReal ≤ 6 * R} ⊆ Ω N := by
      intro p hp
      apply hN
      change g.edist x p ≤ ENNReal.ofReal (6 * R)
      calc
        g.edist x p = ENNReal.ofReal (g.edist x p).toReal :=
          (ENNReal.ofReal_toReal (g.edist_ne_top x p)).symm
        _ ≤ ENNReal.ofReal (6 * R) := ENNReal.ofReal_le_ofReal hp
    obtain ⟨J, hJ⟩ := mem_iUnion.mp (hcover.symm ▸ mem_univ y)
    let E := Real.exp (2 * ((m + 1 : ℕ) : ℝ) * Real.log (b / a) +
      2 * ((m + 1 : ℕ) : ℝ) * ((m : ℝ) * κ) * (b - a) +
      2 * ((m + 1 : ℕ) : ℝ) * e (3 * R) * (b - a) +
      (g.edist x z).toReal ^ 2 / (2 * (b - a)))
    have htail : ∀ᶠ j in atTop, K j a x y ≤ K j b z y * E := by
      refine eventually_atTop.2 ⟨max N J, ?_⟩
      intro j hj
      have hΩj : {p | (g.edist x p).toReal ≤ 6 * R} ⊆ Ω j :=
        hcontains.trans (hΩmono ((le_max_left N J).trans hj))
      have hΩj6 : {p | (g.edist x p).toReal ≤ 2 * (3 * R)} ⊆ Ω j := by
        intro p hp
        apply hΩj
        simpa only [show 2 * (3 * R) = 6 * R by ring] using hp
      have hyj : y ∈ Ω j := hΩmono ((le_max_right N J).trans hj) hJ
      have hxinball : (g.edist x x).toReal ≤ 6 * R := by rw [hxx]; positivity
      obtain ⟨γ, hγ, hγ0, hγ1, hballγ, hspeed⟩ :=
        g.exists_heat_harnack_path hc x x z (by rw [hxx]; positivity) hdist
      have hγΩ : ∀ s ∈ Icc (0 : ℝ) 1, γ s ∈ Ω j := by
        intro s hs
        apply hΩj
        have h3 := hballγ s hs
        exact h3.trans (by nlinarith [hR])
      have hu : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 (m + 1))) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × M => K j p.1 p.2 y) (Ioi 0 ×ˢ Ω j) := by
        intro p hp
        have hs := (hK j).smooth.contMDiffAt (x := ((p.2, y), p.1))
          ((((hΩ j).prod (hΩ j)).prod isOpen_Ioi).mem_nhds ⟨⟨hp.2, hyj⟩, hp.1⟩)
        have hc' := hs.comp p
          ((contMDiffAt_snd.prodMk contMDiffAt_const).prodMk contMDiffAt_fst)
        exact hc'.contMDiffWithinAt
      let f : ℝ × M → ℝ := fun p => Real.log (K j p.1 p.2 y)
      have hbound : ∀ t, 0 < t → ∀ s ∈ Icc (0 : ℝ) 1,
          g.inner (γ s) (D.gradient (fun q => f (t, q)) (γ s))
              (D.gradient (fun q => f (t, q)) (γ s)) -
            2 * deriv (fun r => f (r, γ s)) t ≤
          4 * ((m + 1 : ℕ) : ℝ) / t +
            4 * ((m + 1 : ℕ) : ℝ) * (e (3 * R) + (m : ℝ) * κ) := by
        intro t ht s hs
        have hq := hlocal x (3 * R) (by positivity) (Ω j) (hΩ j) hΩj6
          (fun p => K j p.1 p.2 y) hu
          (fun r hr q hq => (hK j).positive r hr q hq y hyj)
          (fun r hr q hq => (hK j).heat_equation r hr q hq y)
          t ht (γ s)
        have hq' := hq (hballγ s hs)
        simpa only [f] using hq'
      have hf : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 (m + 1))) 𝓘(ℝ, ℝ) ∞ f
          (Ioi 0 ×ˢ Ω j) := by
        intro p hp
        exact (contMDiffAt_log_of_pos
          (hu.contMDiffAt ((isOpen_Ioi.prod (hΩ j)).mem_nhds hp))
          ((hK j).positive p.1 hp.1 p.2 hp.2 y hyj)).contMDiffWithinAt
      have hlog := D.log_harnack_of_gradient_bound_on (hΩ j)
        hf
        hγ hγΩ (c := 2 * ((m + 1 : ℕ) : ℝ))
        (B := 2 * ((m + 1 : ℕ) : ℝ) * (e (3 * R) + (m : ℝ) * κ))
        (L := (g.edist x z).toReal)
        (fun t ht s hs => by
          have hb := hbound t ht s hs
          convert hb using 1 <;> ring)
        (fun s hs => (hspeed s (Ioo_subset_Icc_self hs)).le) ha hab
      rw [hγ0, hγ1] at hlog
      have hhlog : Real.log (K j a x y) ≤ Real.log (K j b z y) +
          (2 * ((m + 1 : ℕ) : ℝ) * Real.log (b / a) +
            2 * ((m + 1 : ℕ) : ℝ) * ((m : ℝ) * κ) * (b - a) +
            2 * ((m + 1 : ℕ) : ℝ) * e (3 * R) * (b - a) +
            (g.edist x z).toReal ^ 2 / (2 * (b - a))) := by
        dsimp [f] at hlog
        convert hlog using 1 <;> ring
      have hh := Real.exp_le_exp.mpr hhlog
      have hzinball : (g.edist x z).toReal ≤ 6 * R := by
        have hz := hballγ 1 (by simp)
        rw [hγ1] at hz
        exact hz.trans (by nlinarith [hR])
      rw [Real.exp_add, Real.exp_log ((hK j).positive a ha x
        (hΩj hxinball) y hyj), Real.exp_log ((hK j).positive b (ha.trans hab) z
        (hΩj hzinball) y hyj)] at hh
      simpa only [E] using hh
    exact le_of_tendsto_of_tendsto (DirichletExhaustion.tendsto_supremum hmono hbdd ha x y)
      ((DirichletExhaustion.tendsto_supremum hmono hbdd (ha.trans hab) z y).mul_const E)
      htail
  have hR0 : 1 ≤ max 1 ((g.edist x z).toReal) := le_max_left _ _
  have hdist0 : (g.edist x z).toReal ≤ max 1 ((g.edist x z).toReal) := le_max_right _ _
  have h3 : Tendsto (fun R : ℝ => e (3 * R)) atTop (𝓝 0) := by
    apply he.comp
    refine tendsto_atTop.2 ?_
    intro C
    filter_upwards [eventually_ge_atTop (max 0 (C / 3))] with R hR
    have hR' : 0 ≤ R := (le_max_left 0 (C / 3)).trans hR
    by_cases hC : C ≤ 0
    · linarith
    · have hCpos : 0 < C := lt_of_not_ge hC
      have hCr : C / 3 ≤ R := (le_max_right 0 (C / 3)).trans hR
      nlinarith
  have hcoef : Tendsto (fun R : ℝ =>
      2 * ((m + 1 : ℕ) : ℝ) * e (3 * R) * (b - a)) atTop (𝓝 0) := by
    simpa using ((tendsto_const_nhds.mul h3).mul tendsto_const_nhds)
  have harg : Tendsto (fun R : ℝ =>
      2 * ((m + 1 : ℕ) : ℝ) * Real.log (b / a) +
          2 * ((m + 1 : ℕ) : ℝ) * ((m : ℝ) * κ) * (b - a) +
          2 * ((m + 1 : ℕ) : ℝ) * e (3 * R) * (b - a) +
          (g.edist x z).toReal ^ 2 / (2 * (b - a))) atTop
      (𝓝 (2 * ((m + 1 : ℕ) : ℝ) * Real.log (b / a) +
          2 * ((m + 1 : ℕ) : ℝ) * ((m : ℝ) * κ) * (b - a) +
          (g.edist x z).toReal ^ 2 / (2 * (b - a)))) := by
    let c1 : ℝ := 2 * ((m + 1 : ℕ) : ℝ) * Real.log (b / a)
    let c2 : ℝ := 2 * ((m + 1 : ℕ) : ℝ) * ((m : ℝ) * κ) * (b - a)
    let c3 : ℝ := (g.edist x z).toReal ^ 2 / (2 * (b - a))
    have harg0 :
        Tendsto (fun R : ℝ => c1 + (c2 + 2 * ((m + 1 : ℕ) : ℝ) * e (3 * R) * (b - a)) + c3)
          atTop (𝓝 (c1 + c2 + c3)) := by
      convert ((hcoef.const_add c2).const_add c1).add
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => c3) atTop (𝓝 c3)) using 1
      simp only [add_zero, add_assoc]
    simpa only [c1, c2, c3, add_assoc] using harg0
  have hE : Tendsto (fun R : ℝ =>
      dirichletExhaustionKernel K b z y * Real.exp
        (2 * ((m + 1 : ℕ) : ℝ) * Real.log (b / a) +
          2 * ((m + 1 : ℕ) : ℝ) * ((m : ℝ) * κ) * (b - a) +
          2 * ((m + 1 : ℕ) : ℝ) * e (3 * R) * (b - a) +
          (g.edist x z).toReal ^ 2 / (2 * (b - a)))) atTop
      (𝓝 (dirichletExhaustionKernel K b z y * E₀)) := by
    apply tendsto_const_nhds.mul
    apply Real.continuous_exp.continuousAt.tendsto.comp harg
  exact ge_of_tendsto hE (eventually_atTop.2 ⟨max 1 ((g.edist x z).toReal),
    fun R hR => hfinite R (hR0.trans hR) (hdist0.trans hR)⟩)

end PoincareConjecture.LeviCivitaData
