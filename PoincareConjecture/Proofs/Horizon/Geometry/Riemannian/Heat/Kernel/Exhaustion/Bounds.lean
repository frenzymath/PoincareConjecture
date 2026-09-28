import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Exhaustion.Properties
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.LiYau.DomainHarnack
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Balls

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology Bundle ENNReal

universe u

namespace PoincareConjecture.LeviCivitaData

set_option backward.isDefEq.respectTransparency false in

theorem exists_dirichletHeatKernel_bound_on_domains_containing_ball
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [PreconnectedSpace M] {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (hn : 0 < n) (hcomplete : MetricComplete g)
    {k : ℝ} (hk : 0 ≤ k)
    (hRic : ∀ x (v : TangentSpace (𝓡 n) x), -k * g.inner x v v ≤ D.ricci x v v)
    (O : M) {R : ℝ} (hR : 1 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ Ω : Set M, IsOpen Ω →
      {z | (g.edist O z).toReal ≤ 15 * R} ⊆ Ω →
      ∀ K : ℝ → M → M → ℝ, Dirichlet.IsDirichletHeatKernel D Ω K →
        ∀ t, 0 < t → ∀ x, (g.edist O x).toReal ≤ R → ∀ y,
          K t x y ≤ Real.exp (2 * (n : ℝ) * Real.log 2 + C * t +
            (2 * R) ^ 2 / (2 * t)) / g.volumeMeasure.real (g.ball O 1) := by
  obtain ⟨C, hC, hH⟩ :=
    D.exists_heat_harnack_on_domains_containing_ball hn hcomplete hk hRic O hR
  refine ⟨C, hC, ?_⟩
  intro Ω hΩ hcontains K hK t ht x hx y
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let E := Real.exp (2 * (n : ℝ) * Real.log 2 + C * t + (2 * R) ^ 2 / (2 * t))
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hfinite := g.volumeMeasure_ball_lt_top hcomplete O 1
  have hvol : 0 < g.volumeMeasure.real (g.ball O 1) :=
    ENNReal.toReal_pos (g.volumeMeasure_ball_pos O zero_lt_one).ne' hfinite.ne
  change K t x y ≤ E / g.volumeMeasure.real (g.ball O 1)
  by_cases hy : y ∈ Ω
  · have hu : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => K p.1 p.2 y) (Ioi 0 ×ˢ Ω) := by
      intro p hp
      have hs := hK.smooth.contMDiffAt (x := ((p.2, y), p.1))
        (((hΩ.prod hΩ).prod isOpen_Ioi).mem_nhds ⟨⟨hp.2, hy⟩, hp.1⟩)
      have hc := hs.comp p
        ((contMDiffAt_snd.prodMk contMDiffAt_const).prodMk contMDiffAt_fst)
      exact hc.contMDiffWithinAt
    have ht2 : 0 < 2 * t := by positivity
    have hsym : (fun z => K (2 * t) z y) = K (2 * t) y := by
      funext z
      exact hK.symmetric (2 * t) ht2 z y
    have hi : Integrable (fun z => K (2 * t) z y) g.volumeMeasure := by
      rw [hsym]
      exact hK.integrable_ambient ht2 y
    have hmass : (∫ z, K (2 * t) z y ∂g.volumeMeasure) ≤ 1 := by
      rw [hsym]
      exact hK.integral_ambient_le_one ht2 y
    have hmeas : MeasurableSet (g.ball O 1) :=
      (isOpen_lt (continuous_const.edist continuous_id) continuous_const).measurableSet
    have hpoint (z : M) (hz : z ∈ g.ball O 1) : K t x y ≤ K (2 * t) z y * E := by
      have hOz : (g.edist O z).toReal < 1 :=
        ENNReal.toReal_lt_of_lt_ofReal (show g.edist O z < ENNReal.ofReal 1 from hz)
      have hxz : (g.edist x z).toReal ≤ 2 * R := by
        have htri := g.toReal_edist_triangle x O z
        have hsymx : g.edist x O = g.edist O x := edist_comm x O
        rw [hsymx] at htri
        linarith
      have hh := hH Ω hΩ hcontains (fun p : ℝ × M => K p.1 p.2 y) hu
        (fun s hs w hw => hK.positive s hs w hw y hy)
        (fun s hs w hw => hK.heat_equation s hs w hw y)
        t (2 * t) ht (by linarith) x z hx (hOz.le.trans hR)
      have htime : 2 * t - t = t := by ring
      have hratio : 2 * t / t = 2 := by field_simp
      rw [htime, hratio] at hh
      apply hh.trans (mul_le_mul_of_nonneg_left ?_ (hK.nonneg (2 * t) ht2 z y))
      apply Real.exp_le_exp.mpr
      gcongr
    have havg := setIntegral_mono_on (integrableOn_const hfinite.ne)
      (hi.mul_const E).integrableOn hmeas hpoint
    have hmassball : (∫ z in g.ball O 1, K (2 * t) z y ∂g.volumeMeasure) ≤ 1 :=
      (setIntegral_le_integral hi (Filter.Eventually.of_forall
        (fun z => hK.nonneg (2 * t) ht2 z y))).trans hmass
    rw [setIntegral_const, integral_mul_const, smul_eq_mul] at havg
    apply (le_div_iff₀ hvol).mpr
    calc
      K t x y * g.volumeMeasure.real (g.ball O 1) ≤
          (∫ z in g.ball O 1, K (2 * t) z y ∂g.volumeMeasure) * E := by
        simpa only [mul_comm] using havg
      _ ≤ 1 * E := mul_le_mul_of_nonneg_right hmassball hE
      _ = E := one_mul E
  · rw [hK.zero_outside t ht x y (Or.inr hy)]
    exact div_nonneg hE hvol.le

end PoincareConjecture.LeviCivitaData
