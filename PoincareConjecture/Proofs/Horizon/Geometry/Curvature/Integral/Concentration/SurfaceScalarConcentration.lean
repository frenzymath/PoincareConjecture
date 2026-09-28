import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.PairedLevelGeometry
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.SurfaceLevels










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open Poincare.CurvatureIntegral Poincare.GromovHausdorff
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Bundle Topology BigOperators


theorem PoincareConjecture.RiemannianMetric.exists_surface_scalar_concentration_at_quarter_spire
    {M : ℕ → Type}
    [∀ j, TopologicalSpace (M j)] [∀ j, T3Space (M j)]
    [∀ j, MeasurableSpace (M j)] [∀ j, BorelSpace (M j)]
    [∀ j, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (M j)]
    [∀ j, IsManifold (𝓡 3) ∞ (M j)] [∀ j, PreconnectedSpace (M j)]
    (g : ∀ j, PoincareConjecture.RiemannianMetric 3 (M j))
    (D : ∀ j, PoincareConjecture.LeviCivitaData (g j))
    (hcomplete : ∀ j, PoincareConjecture.MetricComplete (g j))
    (hsec : ∀ j x (v w : TangentSpace (𝓡 3) x),
      -1 ≤ (D j).sectionalCurvature x v w)
    (p : ∀ j, M j)
    {Y : BasedMetricSpaceBundle.{0}} [ProperSpace Y.carrier]
    (hconv : PointedGHConvergesUnbounded (fun j => (g j).toBasedMetricSpace (p j)) Y)
    (hYgeo : ∀ x y : Y.carrier, ∃ γ : ℝ → Y.carrier,
      γ 0 = x ∧ γ 1 = y ∧
        ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
          dist (γ s) (γ t) = |s - t| * dist x y)
    {δ cminus c cplus cap : ℝ}
    (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 256)
    (hnear : 1 - δ ^ 2 / 8 < cminus) (hminus : cminus < c)
    (hplus : c < cplus) (hplus1 : cplus < 1) (hcap : 0 < cap) (hcap1 : cap ≤ 1)
    {R : ℝ} (hR : 1 < R)
    (hlarge : ∀ K : ℝ, ∃ j,
      K < ∫ x in (g j).ball (p j) 1, (D j).scalarCurvature x ∂(g j).volumeMeasure) :
    ∃ (B : Y.carrier → ℝ) (y : Y.carrier) (b ρ : ℝ)
      (φ : ℕ → ℕ) (ref q : ∀ j, M (φ j)),
      (∀ x, 0 < B x ∧ 2 * B x ≤ cap) ∧
      (∀ x z : Y.carrier, 0 < dist x z → dist x z < 2 * B x →
        HasLocalDistanceAscent cminus x z) ∧
      (∀ x : Y.carrier, ∀ a : ℝ, 0 ≤ a → 2 * a ≤ cap →
        (∀ z : Y.carrier, 0 < dist x z → dist x z < 2 * a →
          HasLocalDistanceAscent cminus x z) → a ≤ B x) ∧
      y ∈ Metric.closedBall Y.base R ∧
      (∀ z : Y.carrier, z ≠ y → B z / 4 ≤ dist z y) ∧
      0 < b ∧ b ≤ cap ∧ 0 < ρ ∧ ρ < b / 8 ∧
      (∀ z : Y.carrier, 0 < dist y z → dist y z ≤ b →
        HasLocalDistanceAscent cplus y z) ∧
      StrictMono φ ∧
      Tendsto (fun j => ((g (φ j)).edist (p (φ j)) (ref j)).toReal)
        atTop (𝓝 (dist Y.base y)) ∧
      PointedGHConvergesUnbounded
        (fun j => (g (φ j)).toBasedMetricSpace (ref j)) (Y.rebase y) ∧
      (∀ j, letI := (g (φ j)).toMetricSpace
        dist (ref j) (q j) ≤ ρ ∧
        badAscentRadius c b (q j) ≤ badAscentRadius c b (ref j) ∧
        ∀ z : M (φ j), dist (ref j) z ≤ ρ →
          badAscentRadius c b (q j) ≤ 2 * badAscentRadius c b z) ∧
      (∀ j, letI := (g (φ j)).toMetricSpace
        0 < badAscentRadius c b (q j)) ∧
      Tendsto (fun j => letI := (g (φ j)).toMetricSpace
        badAscentRadius c b (ref j)) atTop (𝓝 0) ∧
      Tendsto (fun j => letI := (g (φ j)).toMetricSpace
        badAscentRadius c b (q j)) atTop (𝓝 0) ∧
      Tendsto (fun j => ((g (φ j)).edist (ref j) (q j)).toReal) atTop (𝓝 0) ∧
      Tendsto (fun j => letI := (g (φ j)).toMetricSpace
        ∫ x in (g (φ j)).ball (q j) (4 * badAscentRadius c b (q j)),
          (D (φ j)).scalarCurvature x ∂(g (φ j)).volumeMeasure) atTop atTop := by
  classical
  obtain ⟨B, S, b, ρ, φ, ref, q, A, hB, hBasc, hBmax, hS, hb, hbcap, hρ, hρb,
      hstrong, hφ, href, hconvref, hq, hzero, hA, hcover, hmass, rest⟩ :=
    PoincareConjecture.RiemannianMetric.exists_quarter_spire_scalar_concentration_with_controlled_levels
      (m := 1) le_rfl g D hcomplete hsec p hconv hYgeo hδ hδsmall
      hnear hminus hplus hplus1 hcap hcap1 hR hlarge
  let (j : ℕ) := (g (φ j)).toMetricSpace
  obtain ⟨f, u, hf, hu, hgeometry, hlevelGeometry, hconcentration⟩ := rest
  let N := ⌈PoincareConjecture.RiemannianMetric.modelVolume 3 1 3 /
    PoincareConjecture.RiemannianMetric.modelVolume 3 1 (1 / 10485760)⌉₊

  let C : ℝ := 8 * Real.pi * N + 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hind := hconcentration C hC
  obtain ⟨i, ψ, hψ, hpos, hdiv⟩ := hind (by
    apply Filter.Eventually.of_forall
    intro j w
    dsimp only
    intro t ht
    let r := Sum.elim (fun z : A => z.val.2) (fun ir => ir.val.2) w
    have hr : 0 < r ∧ r ≤ 1 / 2 := by
      cases w with
      | inl z => exact ⟨(hA z.val z.property).1, (hA z.val z.property).2.1⟩
      | inr ir => exact ⟨ir.property.1, ir.property.2.1.trans (by linarith)⟩
    obtain ⟨hFu, hproper, hreg, hband, hcore, hball, hrad, hpartners⟩ := hgeometry j w
    have hspeed := fun x hx =>
      let hd := hband x hx
      let h := hcore x hd.1 hd.2
      And.intro h.2.1 h.2.2.1
    have hhess := fun x hx =>
      let hd := hband x hx
      (hcore x hd.1 hd.2).2.2.2.1
    have hparams := (D (φ j)).regularLevel_annular_bounds_with_dimensional_constant_of_quarter_gradient
      (m := 1) (hcomplete (φ j)) (hsec (φ j)) (hf j w)
      (Sum.elim (fun z : A => ref j z.val.1) (fun ir => q j ir.val.1) w)
      hr.1 (by linarith [hr.2]) hproper hspeed hhess hball
    have hβ : 0 ≤ PoincareConjecture.RiemannianMetric.scaleAnnularInductionConstant 1 / t :=
      div_nonneg (PoincareConjecture.RiemannianMetric.scaleAnnularInductionConstant_pos 1).le
        (by linarith [ht.1, hr.1])
    have hs := (D (φ j)).integral_regularLevel_surface_pos_scalar_le
      (hf j w) t (hpartners t ht).1
      (fun x hx => hreg x (by rw [hx]; exact ⟨by linarith [ht.1, hr.1], by linarith [ht.2, hr.1]⟩))
      (K := fun _ => 1) continuousOn_const (fun _ _ => zero_le_one)
      (fun x _ v w => hsec (φ j) x v w) hβ (hparams.2.1 t ht) N
      (hlevelGeometry j w t ht).2.2.1
    have hE : 0 ≤ ∫ z,
        (D (φ j)).levelSectionalError (f j w) (fun _ => 1)
          (PoincareConjecture.RiemannianMetric.scaleAnnularInductionConstant 1 / t)
          (openLevelIncl (f j w) ((g (φ j)).regularDomain (hf j w)) t z)
        ∂(g (φ j)).regularLevelVolume (hf j w) ((g (φ j)).regularDomain (hf j w))
          ((g (φ j)).regularDomain_regular (hf j w)) t :=
      integral_nonneg (fun z =>
        (D (φ j)).levelSectionalError_nonneg (f j w) (fun _ => 1) hβ zero_le_one)
    simp only [Nat.sub_self, pow_zero]
    apply hs.trans
    dsimp [C]
    nlinarith [mul_nonneg (by positivity : 0 ≤ 8 * Real.pi * (N : ℝ)) hE])
  have hi : i.val ∈ Metric.closedBall Y.base R ∧
      ∀ z : Y.carrier, z ≠ i.val → B z / 4 ≤ dist z i.val := by
    have hi' : i.val ∈ (S : Set Y.carrier) := i.property
    rw [hS] at hi'
    exact hi'
  refine ⟨B, i.val, b, ρ, φ ∘ ψ, (fun j => ref (ψ j) i.val), (fun j => q (ψ j) i),
    hB, hBasc, hBmax, hi.1, hi.2, hb, hbcap, hρ, hρb, hstrong i, hφ.comp hψ,
    (href i.val).comp hψ.tendsto_atTop, ?_, (fun j => hq (ψ j) i), hpos,
    (hzero i).1.comp hψ.tendsto_atTop, (hzero i).2.1.comp hψ.tendsto_atTop,
    (hzero i).2.2.comp hψ.tendsto_atTop, hdiv⟩
  intro r hr
  obtain ⟨δ, hδ, hpositive, ⟨⟨C, hC⟩, hdist⟩⟩ := hconvref i.val r hr
  exact ⟨fun j => δ (ψ j), hδ.comp hψ.tendsto_atTop,
    fun j => hpositive (ψ j), ⟨C, fun j => hC (ψ j)⟩,
    hdist.comp hψ.tendsto_atTop⟩
