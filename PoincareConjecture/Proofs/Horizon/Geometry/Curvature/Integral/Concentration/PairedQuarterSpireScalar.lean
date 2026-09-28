import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.PairedScalarSlabs
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.NumericalAnnularCover

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open Poincare.CurvatureIntegral Poincare.Geometry.Manifold.RegularLevel
open Poincare.GromovHausdorff
open scoped Manifold ContDiff Bundle Topology BigOperators
namespace PoincareConjecture.RiemannianMetric
private theorem pointedGHConvergesUnbounded_subseq
    {X : ℕ → BasedMetricSpaceBundle.{0}} {Y : BasedMetricSpaceBundle.{0}}
    (h : PointedGHConvergesUnbounded X Y) (φ : ℕ → ℕ)
    (hφ : Tendsto φ atTop atTop) :
    PointedGHConvergesUnbounded (fun j => X (φ j)) Y := by
  intro r hr
  obtain ⟨δ, hδ, hpos, ⟨⟨C, hC⟩, hdist⟩⟩ := h r hr
  exact ⟨fun j => δ (φ j), hδ.comp hφ, fun j => hpos (φ j),
    ⟨C, fun j => hC (φ j)⟩, hdist.comp hφ⟩

theorem exists_quarter_spire_scalar_concentration_with_level_opposite_partners
    {m : ℕ} (hm : 1 ≤ m) {M : ℕ → Type}
    [∀ j, TopologicalSpace (M j)] [∀ j, T3Space (M j)]
    [∀ j, MeasurableSpace (M j)] [∀ j, BorelSpace (M j)]
    [∀ j, ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) (M j)]
    [∀ j, IsManifold (𝓡 (m + 2)) ∞ (M j)] [∀ j, PreconnectedSpace (M j)]
    (g : ∀ j, RiemannianMetric (m + 2) (M j)) (D : ∀ j, LeviCivitaData (g j))
    (hcomplete : ∀ j, MetricComplete (g j))
    (hsec : ∀ j x (v w : TangentSpace (𝓡 (m + 2)) x),
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
    ∃ (B : Y.carrier → ℝ) (S : Finset Y.carrier) (b ρ : ℝ)
      (φ : ℕ → ℕ) (ref : ∀ j, Y.carrier → M (φ j))
      (q : ∀ j, S → M (φ j)) (A : Finset (Y.carrier × ℝ)),
      (∀ x, 0 < B x ∧ 2 * B x ≤ cap) ∧
      (∀ x y : Y.carrier, 0 < dist x y → dist x y < 2 * B x →
        HasLocalDistanceAscent cminus x y) ∧
      (∀ x : Y.carrier, ∀ a : ℝ, 0 ≤ a → 2 * a ≤ cap →
        (∀ y : Y.carrier, 0 < dist x y → dist x y < 2 * a →
          HasLocalDistanceAscent cminus x y) → a ≤ B x) ∧
      (S : Set Y.carrier) =
        {x | x ∈ Metric.closedBall Y.base R ∧ ∀ y : Y.carrier, y ≠ x → B y / 4 ≤ dist y x} ∧
      0 < b ∧ b ≤ cap ∧ 0 < ρ ∧ ρ < b / 8 ∧
      (∀ i : S, ∀ y : Y.carrier, 0 < dist i.val y → dist i.val y ≤ b →
        HasLocalDistanceAscent cplus i.val y) ∧
      StrictMono φ ∧
      (∀ y : Y.carrier,
        Tendsto (fun j => ((g (φ j)).edist (p (φ j)) (ref j y)).toReal)
          atTop (𝓝 (dist Y.base y))) ∧
      (∀ y : Y.carrier,
        PointedGHConvergesUnbounded
          (fun j => (g (φ j)).toBasedMetricSpace (ref j y)) (Y.rebase y)) ∧
      (∀ j, ∀ i : S, letI := (g (φ j)).toMetricSpace
        dist (ref j i.val) (q j i) ≤ ρ ∧
        badAscentRadius c b (q j i) ≤ badAscentRadius c b (ref j i.val) ∧
        ∀ z : M (φ j), dist (ref j i.val) z ≤ ρ →
          badAscentRadius c b (q j i) ≤ 2 * badAscentRadius c b z) ∧
      (∀ i : S,
        Tendsto (fun j => letI := (g (φ j)).toMetricSpace
          badAscentRadius c b (ref j i.val)) atTop (𝓝 0) ∧
        Tendsto (fun j => letI := (g (φ j)).toMetricSpace
          badAscentRadius c b (q j i)) atTop (𝓝 0) ∧
        Tendsto (fun j => ((g (φ j)).edist (ref j i.val) (q j i)).toReal)
          atTop (𝓝 0)) ∧
      (∀ z ∈ A, 0 < z.2 ∧ z.2 ≤ 1 / 2 ∧ 3 * z.2 < 2 * B z.1) ∧
      (∀ j, (g (φ j)).ball (p (φ j)) 1 ⊆
        (⋃ z : A, {x : M (φ j) | ((g (φ j)).edist (ref j z.val.1) x).toReal ∈
          Icc (113 * z.val.2 / 96) (19 * z.val.2 / 16)}) ∪
            ⋃ i : S, (g (φ j)).ball (q j i) (b / 12)) ∧
      Tendsto (fun j => ∫ x in (g (φ j)).ball (p (φ j)) 1,
        (D (φ j)).scalarCurvature x ∂(g (φ j)).volumeMeasure) atTop atTop ∧
    letI (j : ℕ) := (g (φ j)).toMetricSpace
    let τ := 1 / (1 + δ ^ 2 / 8)
    let a := fun j i => badAscentRadius c b (q j i)
    let T := fun j => A ⊕ {ir : S × ℝ // 0 < ir.2 ∧ ir.2 ≤ b / 6 ∧ 2 * a j ir.1 ≤ ir.2}
    let center := fun j => Sum.elim (fun z : A => ref j z.val.1) (fun ir : {ir : S × ℝ //
      0 < ir.2 ∧ ir.2 ≤ b / 6 ∧ 2 * a j ir.1 ≤ ir.2} => q j ir.val.1)
    let radius := fun j => Sum.elim (fun z : A => z.val.2) (fun ir : {ir : S × ℝ //
      0 < ir.2 ∧ ir.2 ≤ b / 6 ∧ 2 * a j ir.1 ≤ ir.2} => ir.val.2)
    ∃ (f u : ∀ j, T j → M (φ j) → ℝ)
      (hf : ∀ j w, ContMDiff (𝓡 (m + 2)) 𝓘(ℝ, ℝ) ∞ (f j w))
      (_hu : ∀ j w, ContMDiff (𝓡 (m + 2)) 𝓘(ℝ, ℝ) ∞ (u j w)),
      (∀ j w, let r := radius j w
        let ε := δ ^ 4 * r / 1048576
        let s := τ * r / 1024
        let I := Ioo (9 * r / 16) (15 * r / 16)
      (∀ x, (f j w) x = (u j w) x / (2 * τ)) ∧
      IsProperMap (I.restrictPreimage (f j w)) ∧
      (∀ x : (M (φ j)), (f j w) x ∈ I → mfderiv (𝓡 (m + 2)) 𝓘(ℝ, ℝ) (f j w) x ≠ 0) ∧
      (∀ x : (M (φ j)), (f j w) x ∈ I →
        r < ((g (φ j)).edist (center j w) x).toReal ∧ ((g (φ j)).edist (center j w) x).toReal < 2 * r) ∧
      (∀ x : (M (φ j)), r < ((g (φ j)).edist (center j w) x).toReal → ((g (φ j)).edist (center j w) x).toReal < 2 * r →
        |(f j w) x - ((g (φ j)).edist (center j w) x).toReal / 2| ≤ ε / 2 ∧
        (1 / 4 : ℝ) ≤ (g (φ j)).tangentNorm x ((D (φ j)).gradient (f j w) x) ∧
        (g (φ j)).tangentNorm x ((D (φ j)).gradient (f j w) x) ≤ 1 ∧
        (∀ v : TangentSpace (𝓡 (m + 2)) x,
          (D (φ j)).hessian (f j w) x v v ≤ (5 / r) * (g (φ j)).inner x v v) ∧
        1 - δ ^ 2 ≤ (g (φ j)).tangentNorm x ((D (φ j)).gradient (u j w) x) ∧
        (g (φ j)).tangentNorm x ((D (φ j)).gradient (u j w) x) ≤ 1 ∧
        ∀ v : TangentSpace (𝓡 (m + 2)) x,
          (D (φ j)).hessian (u j w) x v v ≤ (5 / r) * (g (φ j)).inner x v v) ∧
      (f j w) ⁻¹' Icc (55 * r / 96) (9 * r / 10) ⊆ (g (φ j)).ball (center j w) (2 * r) ∧
      {x : (M (φ j)) | ((g (φ j)).edist (center j w) x).toReal ∈ Icc (113 * r / 96) (19 * r / 16)} ⊆
        (f j w) ⁻¹' Icc (7 * r / 12) (3 * r / 5) ∧
      ∀ t ∈ Icc (7 * r / 12) (9 * r / 10),
        IsCompact ((f j w) ⁻¹' {t}) ∧
        ∃ h : (M (φ j)) → ℝ, ContMDiff (𝓡 (m + 2)) 𝓘(ℝ, ℝ) ∞ h ∧
          let U := (u j w) ⁻¹' Ioo (2 * τ * t - s / 4) (2 * τ * t + s / 4)
          (∀ x : (M (φ j)), (f j w) x = t → Metric.closedBall x (s / 16) ⊆ U) ∧
          ∀ x ∈ U,
            (1 / 2 : ℝ) ≤ (g (φ j)).tangentNorm x ((D (φ j)).gradient (u j w) x) ∧
            (g (φ j)).tangentNorm x ((D (φ j)).gradient (u j w) x) ≤ 1 ∧
            (1 / 2 : ℝ) ≤ (g (φ j)).tangentNorm x ((D (φ j)).gradient h x) ∧
            (g (φ j)).tangentNorm x ((D (φ j)).gradient h x) ≤ 1 ∧
            (g (φ j)).inner x ((D (φ j)).gradient (u j w) x) ((D (φ j)).gradient h x) ≤ -1 + 128 * δ ∧
            ∀ v : TangentSpace (𝓡 (m + 2)) x,
              (D (φ j)).hessian (u j w) x v v ≤ (3 / s) * (g (φ j)).inner x v v ∧
              (D (φ j)).hessian h x v v ≤ (3 / s) * (g (φ j)).inner x v v) ∧
      ∀ C : ℝ, 0 ≤ C →
        (∀ᶠ j in atTop, ∀ w : T j,
          let r := radius j w
          let U := (g (φ j)).regularDomain (hf j w)
          letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 2))) = m + 2) :=
            ⟨finrank_euclideanSpace_fin⟩
          letI (t : ℝ) := openLevelSetChartedSpace (hf j w) U
            ((g (φ j)).regularDomain_regular (hf j w)) (m + 1) t
          letI (t : ℝ) := isManifold_openLevelSet (hf j w) U
            ((g (φ j)).regularDomain_regular (hf j w)) (m + 1) t
          let DL := fun t => (RiemannianMetric.regularLevelMetric
            (hf j w) U ((g (φ j)).regularDomain_regular (hf j w)) t (g (φ j))).leviCivitaData
          ∀ t ∈ Icc (7 * r / 12) (9 * r / 10),
            (∫ z, max 0 ((DL t).scalarCurvature z)
              ∂(g (φ j)).regularLevelVolume (hf j w) U ((g (φ j)).regularDomain_regular (hf j w)) t) ≤
            C * (r ^ (m - 1) + ∫ z,
              (D (φ j)).levelSectionalError (f j w) (fun _ => 1)
                (scaleAnnularInductionConstant m / t) (openLevelIncl (f j w) U t z)
              ∂(g (φ j)).regularLevelVolume (hf j w) U ((g (φ j)).regularDomain_regular (hf j w)) t)) →
        ∃ i : S, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
          (∀ j, 0 < a (ψ j) i) ∧
          Tendsto (fun j => ∫ x in (g (φ (ψ j))).ball (q (ψ j) i) (4 * a (ψ j) i),
            (D (φ (ψ j))).scalarCurvature x ∂(g (φ (ψ j))).volumeMeasure) atTop atTop := by
  classical
  let (j : ℕ) := (g j).toMetricSpace

  obtain ⟨ψ, hψ, hψlarge⟩ := exists_strictMono_above_thresholds
    (fun j => ∫ x in (g j).ball (p j) 1, (D j).scalarCurvature x ∂(g j).volumeMeasure)
    (fun j => (j : ℝ)) hlarge
  have hmass : Tendsto (fun j => ∫ x in (g (ψ j)).ball (p (ψ j)) 1,
      (D (ψ j)).scalarCurvature x ∂(g (ψ j)).volumeMeasure) atTop atTop :=
    tendsto_atTop_mono (fun j => (hψlarge j).le) tendsto_natCast_atTop_atTop
  have hconvψ := pointedGHConvergesUnbounded_subseq hconv ψ hψ.tendsto_atTop
  obtain ⟨B, F, S, b, ρ, χ, ref, q, hB, hBasc, hBmax, hS, _,
      hb, hbcap, hρ, hρb, hstrong, hχ, _, hfrad, hfconv, hq, hzero, hcover⟩ :=
    exists_quarter_spire_annular_source_cover_of_pointed_limit
      (fun j => g (ψ j)) (fun j => D (ψ j)) (fun j => hcomplete (ψ j))
      (fun j => hsec (ψ j)) (fun j => p (ψ j)) hconvψ hYgeo
      hnear (by nlinarith : 0 ≤ cminus) hminus hplus hplus1 hcap
      (hcap1.trans (by norm_num)) hR
  obtain ⟨A, hA, _, hevent⟩ := hcover (fun _ => b / 12) (fun _ => by positivity)
  obtain ⟨J, hJ⟩ := eventually_atTop.mp hevent
  let φ := fun j => ψ (χ (j + J))
  have hφ : StrictMono φ :=
    hψ.comp (hχ.comp (fun x y hxy => Nat.add_lt_add_right hxy J))
  have hmassφ : Tendsto (fun j => ∫ x in (g (φ j)).ball (p (φ j)) 1,
      (D (φ j)).scalarCurvature x ∂(g (φ j)).volumeMeasure) atTop atTop :=
    (hmass.comp hχ.tendsto_atTop).comp (tendsto_add_atTop_nat J)
  have hcov (j : ℕ) : (g (φ j)).ball (p (φ j)) 1 ⊆
      (⋃ z : A, {x : M (φ j) | ((g (φ j)).edist (ref (j + J) z.val.1) x).toReal ∈
        Icc (113 * z.val.2 / 96) (19 * z.val.2 / 16)}) ∪
          ⋃ i : S, (g (φ j)).ball (q (j + J) i) (b / 12) := by
    intro x hx
    have hx' : x ∈ Metric.ball (p (φ j)) 1 := by
      simpa only [(g (φ j)).toMetricSpace_ball] using hx
    rcases (hJ (j + J) (by omega)).1 hx' with hord | hcrit
    · obtain ⟨z, hz, hlo, hhi⟩ := mem_iUnion₂.mp hord
      apply Or.inl
      refine mem_iUnion.mpr ⟨⟨z, hz⟩, ?_, ?_⟩
      · change 113 * z.2 / 96 ≤ dist (ref (j + J) z.1) x
        convert hlo using 1
        ring
      · change dist (ref (j + J) z.1) x ≤ 19 * z.2 / 16
        convert hhi using 1
        ring
    · apply Or.inr
      simpa only [(g (φ j)).toMetricSpace_ball] using hcrit
  have hasc (j : ℕ) (z : A) :
      ∀ x : M (φ j), z.val.2 / 2 < dist (ref (j + J) z.val.1) x →
        dist (ref (j + J) z.val.1) x < 3 * z.val.2 →
          HasLocalDistanceAscent (1 - δ ^ 2 / 8) (ref (j + J) z.val.1) x := by
    intro x hlo hhi
    exact (hJ (j + J) (by omega)).2 z.val z.property x hlo.le hhi.le
  refine ⟨B, S, b, ρ, φ, fun j => ref (j + J), fun j => q (j + J), A,
    hB, hBasc, hBmax, hS, hb, hbcap, hρ, hρb, hstrong, hφ,
    (fun y => (hfrad y).comp (tendsto_add_atTop_nat J)),
    (fun y => pointedGHConvergesUnbounded_subseq (hfconv y)
      (fun j => j + J) (tendsto_add_atTop_nat J)),
    (fun j i => hq (j + J) i), ?_,
    (fun z hz => ⟨(hA z hz).2.1, by
      have hzB := (hA z hz).2.2.2
      have hBcap := (hB z.1).2
      linarith, (hA z hz).2.2.2⟩), hcov, hmassφ, ?_⟩
  · intro i
    exact ⟨(hzero i).1.comp (tendsto_add_atTop_nat J),
      (hzero i).2.1.comp (tendsto_add_atTop_nat J),
      (hzero i).2.2.comp (tendsto_add_atTop_nat J)⟩
  · exact exists_critical_ball_concentration_with_level_opposite_partners hm
      (fun j => g (φ j)) (fun j => D (φ j)) (fun j => hcomplete (φ j))
      (fun j => hsec (φ j)) (fun j => p (φ j))
      (fun j (z : A) => ref (j + J) z.val.1) (fun z : A => z.val.2)
      (fun j => q (j + J)) hδ hδsmall hb
      (hbcap.trans (hcap1.trans (by norm_num)))
      (hnear.trans hminus).le
      (fun z : A => ⟨(hA z.val z.property).2.1, (hA z.val z.property).2.2.1⟩)
      hasc hcov hmassφ

end PoincareConjecture.RiemannianMetric
