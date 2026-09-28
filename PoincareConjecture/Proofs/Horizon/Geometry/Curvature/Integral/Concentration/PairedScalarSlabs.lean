import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.MixedAnnuli
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.CriticalAnnuli
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.AnnularPair
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.ScaleScalarFunction







noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open Poincare.CurvatureIntegral Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Bundle Topology BigOperators
namespace PoincareConjecture.RiemannianMetric


theorem exists_critical_ball_concentration_with_level_opposite_partners
    {m : ℕ} (hm : 1 ≤ m) {M : ℕ → Type*}
    [∀ j, TopologicalSpace (M j)] [∀ j, T3Space (M j)]
    [∀ j, MeasurableSpace (M j)] [∀ j, BorelSpace (M j)]
    [∀ j, ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) (M j)]
    [∀ j, IsManifold (𝓡 (m + 2)) ∞ (M j)] [∀ j, PreconnectedSpace (M j)]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (g : ∀ j, RiemannianMetric (m + 2) (M j)) (D : ∀ j, LeviCivitaData (g j))
    (hcomplete : ∀ j, MetricComplete (g j))
    (hsec : ∀ j x (v w : TangentSpace (𝓡 (m + 2)) x),
      -1 ≤ (D j).sectionalCurvature x v w)
    (p : ∀ j, M j) (o : ∀ j, κ → M j) (s : κ → ℝ) (q : ∀ j, ι → M j)
    {b c δ : ℝ} (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 256)
    (hb : 0 < b) (hb2 : b ≤ 2) (hc : 1 - δ ^ 2 / 8 ≤ c)
    (hs : ∀ i, 0 < s i ∧ s i ≤ 1)
    (hascent : ∀ j i, letI := (g j).toMetricSpace
      ∀ x : M j, s i / 2 < dist (o j i) x → dist (o j i) x < 3 * s i →
        HasLocalDistanceAscent (1 - δ ^ 2 / 8) (o j i) x)
    (hcover : ∀ j, (g j).ball (p j) 1 ⊆
      (⋃ i, {x : M j | ((g j).edist (o j i) x).toReal ∈
        Icc (113 * s i / 96) (19 * s i / 16)}) ∪
          ⋃ i, (g j).ball (q j i) (b / 12))
    (hlarge : Tendsto (fun j => ∫ x in (g j).ball (p j) 1,
      (D j).scalarCurvature x ∂(g j).volumeMeasure) atTop atTop) :
    letI (j : ℕ) := (g j).toMetricSpace
    let τ := 1 / (1 + δ ^ 2 / 8)
    let a := fun j i => badAscentRadius c b (q j i)
    let T := fun j => κ ⊕ {ir : ι × ℝ // 0 < ir.2 ∧ ir.2 ≤ b / 6 ∧ 2 * a j ir.1 ≤ ir.2}
    let center := fun j => Sum.elim (o j) (fun ir : {ir : ι × ℝ //
      0 < ir.2 ∧ ir.2 ≤ b / 6 ∧ 2 * a j ir.1 ≤ ir.2} => q j ir.val.1)
    let radius := fun j => Sum.elim s (fun ir : {ir : ι × ℝ //
      0 < ir.2 ∧ ir.2 ≤ b / 6 ∧ 2 * a j ir.1 ≤ ir.2} => ir.val.2)
    ∃ (f u : ∀ j, T j → M j → ℝ)
      (hf : ∀ j w, ContMDiff (𝓡 (m + 2)) 𝓘(ℝ, ℝ) ∞ (f j w))
      (_hu : ∀ j w, ContMDiff (𝓡 (m + 2)) 𝓘(ℝ, ℝ) ∞ (u j w)),
      (∀ j w, let r := radius j w
        let ε := δ ^ 4 * r / 1048576
        let s := τ * r / 1024
        let I := Ioo (9 * r / 16) (15 * r / 16)
      (∀ x, (f j w) x = (u j w) x / (2 * τ)) ∧
      IsProperMap (I.restrictPreimage (f j w)) ∧
      (∀ x : (M j), (f j w) x ∈ I → mfderiv (𝓡 (m + 2)) 𝓘(ℝ, ℝ) (f j w) x ≠ 0) ∧
      (∀ x : (M j), (f j w) x ∈ I →
        r < ((g j).edist (center j w) x).toReal ∧ ((g j).edist (center j w) x).toReal < 2 * r) ∧
      (∀ x : (M j), r < ((g j).edist (center j w) x).toReal → ((g j).edist (center j w) x).toReal < 2 * r →
        |(f j w) x - ((g j).edist (center j w) x).toReal / 2| ≤ ε / 2 ∧
        (1 / 4 : ℝ) ≤ (g j).tangentNorm x ((D j).gradient (f j w) x) ∧
        (g j).tangentNorm x ((D j).gradient (f j w) x) ≤ 1 ∧
        (∀ v : TangentSpace (𝓡 (m + 2)) x,
          (D j).hessian (f j w) x v v ≤ (5 / r) * (g j).inner x v v) ∧
        1 - δ ^ 2 ≤ (g j).tangentNorm x ((D j).gradient (u j w) x) ∧
        (g j).tangentNorm x ((D j).gradient (u j w) x) ≤ 1 ∧
        ∀ v : TangentSpace (𝓡 (m + 2)) x,
          (D j).hessian (u j w) x v v ≤ (5 / r) * (g j).inner x v v) ∧
      (f j w) ⁻¹' Icc (55 * r / 96) (9 * r / 10) ⊆ (g j).ball (center j w) (2 * r) ∧
      {x : (M j) | ((g j).edist (center j w) x).toReal ∈ Icc (113 * r / 96) (19 * r / 16)} ⊆
        (f j w) ⁻¹' Icc (7 * r / 12) (3 * r / 5) ∧
      ∀ t ∈ Icc (7 * r / 12) (9 * r / 10),
        IsCompact ((f j w) ⁻¹' {t}) ∧
        ∃ h : (M j) → ℝ, ContMDiff (𝓡 (m + 2)) 𝓘(ℝ, ℝ) ∞ h ∧
          let U := (u j w) ⁻¹' Ioo (2 * τ * t - s / 4) (2 * τ * t + s / 4)
          (∀ x : (M j), (f j w) x = t → Metric.closedBall x (s / 16) ⊆ U) ∧
          ∀ x ∈ U,
            (1 / 2 : ℝ) ≤ (g j).tangentNorm x ((D j).gradient (u j w) x) ∧
            (g j).tangentNorm x ((D j).gradient (u j w) x) ≤ 1 ∧
            (1 / 2 : ℝ) ≤ (g j).tangentNorm x ((D j).gradient h x) ∧
            (g j).tangentNorm x ((D j).gradient h x) ≤ 1 ∧
            (g j).inner x ((D j).gradient (u j w) x) ((D j).gradient h x) ≤ -1 + 128 * δ ∧
            ∀ v : TangentSpace (𝓡 (m + 2)) x,
              (D j).hessian (u j w) x v v ≤ (3 / s) * (g j).inner x v v ∧
              (D j).hessian h x v v ≤ (3 / s) * (g j).inner x v v) ∧
      ∀ C : ℝ, 0 ≤ C →
        (∀ᶠ j in atTop, ∀ w : T j,
          let r := radius j w
          let U := (g j).regularDomain (hf j w)
          letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 2))) = m + 2) :=
            ⟨finrank_euclideanSpace_fin⟩
          letI (t : ℝ) := openLevelSetChartedSpace (hf j w) U
            ((g j).regularDomain_regular (hf j w)) (m + 1) t
          letI (t : ℝ) := isManifold_openLevelSet (hf j w) U
            ((g j).regularDomain_regular (hf j w)) (m + 1) t
          let DL := fun t => (RiemannianMetric.regularLevelMetric
            (hf j w) U ((g j).regularDomain_regular (hf j w)) t (g j)).leviCivitaData
          ∀ t ∈ Icc (7 * r / 12) (9 * r / 10),
            (∫ z, max 0 ((DL t).scalarCurvature z)
              ∂(g j).regularLevelVolume (hf j w) U ((g j).regularDomain_regular (hf j w)) t) ≤
            C * (r ^ (m - 1) + ∫ z,
              (D j).levelSectionalError (f j w) (fun _ => 1)
                (scaleAnnularInductionConstant m / t) (openLevelIncl (f j w) U t z)
              ∂(g j).regularLevelVolume (hf j w) U ((g j).regularDomain_regular (hf j w)) t)) →
        ∃ i : ι, ∃ φ : ℕ → ℕ, StrictMono φ ∧
          (∀ j, 0 < a (φ j) i) ∧
          Tendsto (fun j => ∫ x in (g (φ j)).ball (q (φ j) i) (4 * a (φ j) i),
            (D (φ j)).scalarCurvature x ∂(g (φ j)).volumeMeasure) atTop atTop := by
  classical
  let (j : ℕ) := (g j).toMetricSpace
  dsimp only
  let τ := 1 / (1 + δ ^ 2 / 8)
  let a := fun j i => badAscentRadius c b (q j i)
  let T := fun j => κ ⊕ {ir : ι × ℝ // 0 < ir.2 ∧ ir.2 ≤ b / 6 ∧ 2 * a j ir.1 ≤ ir.2}
  let center := fun j => Sum.elim (o j) (fun ir : {ir : ι × ℝ //
    0 < ir.2 ∧ ir.2 ≤ b / 6 ∧ 2 * a j ir.1 ≤ ir.2} => q j ir.val.1)
  let radius := fun j => Sum.elim s (fun ir : {ir : ι × ℝ //
    0 < ir.2 ∧ ir.2 ≤ b / 6 ∧ 2 * a j ir.1 ≤ ir.2} => ir.val.2)
  have hr (j : ℕ) (w : T j) : 0 < radius j w ∧ radius j w ≤ 1 := by
    cases w with
    | inl i => exact hs i
    | inr ir =>
      exact ⟨ir.property.1, ir.property.2.1.trans (by linarith)⟩
  have hasc (j : ℕ) (w : T j) :
      ∀ x : M j, radius j w / 2 < dist (center j w) x →
        dist (center j w) x < 3 * radius j w →
          HasLocalDistanceAscent (1 - δ ^ 2 / 8) (center j w) x := by
    cases w with
    | inl i => exact hascent j i
    | inr ir =>
      exact hasLocalDistanceAscent_on_annulus_of_two_mul_badAscentRadius_le
        hc ir.property.2.2 ir.property.2.1 (by linarith : 3 * (b / 6) ≤ b)
  have hslab := fun (j : ℕ) (w : T j) =>
    (g j).exists_annular_slab_with_level_opposite_partners
      (D j) (hcomplete j) (hsec j) (center j w) (hr j w).1 (hr j w).2
      hδ hδsmall (hasc j w)
  choose f u hf hu hidentity hproper hreg hband hcore hball hradial hpartners using hslab
  have hbound (j : ℕ) (w : T j) :=
    (g j).radial_annulus_scalar_bound_of_quarter_gradient hm
      (D j) (hcomplete j) (hsec j) (center j w) (hr j w).1 (hr j w).2
      (hf j w) (hproper j w) (hreg j w)
      (fun x hx => ⟨(hcore j w x (hband j w x hx).1 (hband j w x hx).2).2.1,
        (hcore j w x (hband j w x hx).1 (hband j w x hx).2).2.2.1⟩)
      (fun x hx => (hcore j w x (hband j w x hx).1 (hband j w x hx).2).2.2.2.1)
      (hball j w) (hradial j w)
  refine ⟨f, u, hf, hu, ?_, ?_⟩
  · intro j w
    exact ⟨hidentity j w, hproper j w, hreg j w, hband j w, hcore j w,
      hball j w, hradial j w, hpartners j w⟩
  · intro C hC hlevel
    apply PoincareConjecture.exists_subseq_critical_ball_scalar_integral_tendsto_atTop_of_mixed_annuli
      g D p o s (fun i => scaleScalarAnnulusConstant m C * s i ^ m)
      q a (fun _ => b / 6) (fun _ => b / 12) (fun _ => scaleScalarAnnulusConstant m C)
      (by omega) hm hcomplete hsec hb
      (fun j i => badAscentRadius_nonneg c b (q j i))
      (fun j i => badAscentRadius_le hb.le (q j i))
      (fun _ => by positivity) (fun _ => by linarith)
      (fun _ => (scaleScalarAnnulusConstant_pos m hC).le) ?_ hlarge
    filter_upwards [hlevel] with j hj
    refine ⟨hcover j, ?_, ?_⟩
    · intro i
      exact hbound j (.inl i) C hC (hj (.inl i))
    · intro i r hrpos hinner houter
      let w : T j := .inr ⟨(i, r), hrpos, houter, hinner⟩
      exact hbound j w C hC (hj w)

end PoincareConjecture.RiemannianMetric
