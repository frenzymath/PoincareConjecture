import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.PairedQuarterSpireScalar
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.AnnularComponents

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open Poincare.CurvatureIntegral Poincare.Geometry.Manifold.RegularLevel
open Poincare.GromovHausdorff
open scoped Manifold ContDiff Bundle Topology BigOperators
namespace PoincareConjecture.RiemannianMetric

theorem exists_quarter_spire_scalar_concentration_with_controlled_levels
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
      (∀ j w, let r := radius j w
        ∀ t ∈ Icc (7 * r / 12) (9 * r / 10),
          let U := (g (φ j)).regularDomain (hf j w)
          let hreg := (g (φ j)).regularDomain_regular (hf j w)
          letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 2))) = m + 2) :=
            ⟨finrank_euclideanSpace_fin⟩
          letI := openLevelSetChartedSpace (hf j w) U hreg (m + 1) t
          letI := isManifold_openLevelSet (hf j w) U hreg (m + 1) t
          let L := openLevelSet (f j w) U t
          let gL := (g (φ j)).regularLevelMetric (hf j w) U hreg t
          let N := ⌈modelVolume (m + 2) 1 3 / modelVolume (m + 2) 1 (1 / 10485760)⌉₊
          MetricComplete gL ∧ Finite (ConnectedComponents L) ∧
            Nat.card (ConnectedComponents L) ≤ N ∧
            ∀ x y : L, y ∈ connectedComponent x →
              gL.edist x y ≤ ENNReal.ofReal ((N : ℝ) * 36 * Real.exp (3 / 10) * r)) ∧
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
  obtain ⟨B,S,b,ρ,φ,ref,q,A,hB,hBasc,hBmax,hS,hb,hbcap,hρ,hρb,
      hstrong,hφ,href,hconvref,hq,hzero,hA,hcover,hmass,rest⟩ :=
    exists_quarter_spire_scalar_concentration_with_level_opposite_partners hm
      g D hcomplete hsec p hconv hYgeo hδ hδsmall hnear hminus hplus hplus1
      hcap hcap1 hR hlarge
  let (j:ℕ) := (g (φ j)).toMetricSpace
  obtain ⟨f,u,hf,hu,hgeometry,hconcentration⟩ := rest
  refine ⟨B,S,b,ρ,φ,ref,q,A,hB,hBasc,hBmax,hS,hb,hbcap,hρ,hρb,hstrong,hφ,
    href,hconvref,hq,hzero,hA,hcover,hmass,f,u,hf,hu,hgeometry,?_,hconcentration⟩
  intro j w
  dsimp only
  intro t ht
  let r := Sum.elim (fun z:A => z.val.2) (fun ir => ir.val.2) w
  have hr : 0<r ∧ r≤1/2 := by
    cases w with
    | inl z => exact ⟨(hA z.val z.property).1,(hA z.val z.property).2.1⟩
    | inr ir =>
      exact ⟨ir.property.1,ir.property.2.1.trans (by linarith)⟩
  let τ : ℝ := 1/(1+δ^2/8)
  have hτ : 0<τ := by dsimp [τ]; positivity
  have hτ1 : τ≤1 := by
    dsimp [τ]
    apply (div_le_one (by positivity)).mpr
    nlinarith [sq_nonneg δ]
  have hτhalf : (1/2:ℝ)≤τ := by
    dsimp [τ]
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith
  obtain ⟨hFu,hproper,hreg,hband,hcore,hball,hrad,hpartners⟩ := hgeometry j w
  obtain ⟨hcompact,h,hh,hbuffer,hgrad⟩ := hpartners t ht
  let U : TopologicalSpace.Opens (M (φ j)) :=
    ⟨u j w ⁻¹' Ioo (2*τ*t-(τ*r/1024)/4) (2*τ*t+(τ*r/1024)/4),
      isOpen_Ioo.preimage (hu j w).continuous⟩
  apply (g (φ j)).regularLevel_geometry_of_annular_opposite_partner (D (φ j))
    (hcomplete (φ j)) (hsec (φ j)) (hf j w) (hu j w) hh U
    hr.1 hr.2 hτhalf hτ1 hFu (Sum.elim (fun z:A => ref j z.val.1)
      (fun ir => q j ir.val.1) w) t
  · intro x hx
    apply hreg
    rw [hx]
    exact ⟨by linarith [ht.1],by linarith [ht.2]⟩
  · intro x hx
    apply hball
    change f j w x∈Icc (55*r/96) (9*r/10)
    rw [hx]
    exact ⟨by linarith [ht.1],ht.2⟩
  · intro x hx y hy
    apply hbuffer x hx
    change dist y x≤(τ*r/1024)/16
    rw [dist_comm]
    change (g (φ j)).edist x y≤ENNReal.ofReal ((τ*r/1024)/16) at hy
    change ((g (φ j)).edist x y).toReal≤_
    exact (ENNReal.toReal_le_toReal ((g (φ j)).edist_ne_top x y)
      ENNReal.ofReal_ne_top).mpr hy |>.trans_eq (ENNReal.toReal_ofReal (by have hrpos := hr.1; positivity))
  · intro x hx
    obtain ⟨h1,h2,h3,h4,h5,h6⟩ := hgrad x hx
    exact ⟨h1,h2,h3,h4,by linarith,h6⟩

end PoincareConjecture.RiemannianMetric
