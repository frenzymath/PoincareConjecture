import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.Components
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.Diameter
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.RegularLevelDistance
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.Complete











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter PoincareConjecture
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Topology Bundle



theorem PoincareConjecture.LeviCivitaData.regularLevel_components_and_diameter_of_opposite_gradients
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [MeasurableSpace M] [BorelSpace M] [T3Space M] [PreconnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
    [IsManifold (𝓡 (n + 1)) ∞ M]
    {g : PoincareConjecture.RiemannianMetric (n + 1) M}
    (D : PoincareConjecture.LeviCivitaData g) {f h : M → ℝ}
    (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f)
    (hh : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ h)
    (U : TopologicalSpace.Opens M) {H r : ℝ}
    (hH : 0 ≤ H) (hr : 0 < r) (hr1 : r ≤ 1)
    (hfgrad : ∀ y ∈ U, (1 / 2 : ℝ) ≤ g.tangentNorm y (D.gradient f y) ∧
      g.tangentNorm y (D.gradient f y) ≤ 1)
    (hhgrad : ∀ y ∈ U, (1 / 2 : ℝ) ≤ g.tangentNorm y (D.gradient h y) ∧
      g.tangentNorm y (D.gradient h y) ≤ 1)
    (hpair : ∀ y ∈ U,
      g.inner y (D.gradient f y) (D.gradient h y) ≤ -(1 / 8 : ℝ))
    (hfhess : ∀ y ∈ U, ∀ v : TangentSpace (𝓡 (n + 1)) y,
      mvfderiv (𝓡 (n + 1)) f y v = 0 →
        D.hessian f y v v ≤ H * g.inner y v v)
    (hhhess : ∀ y ∈ U, ∀ v : TangentSpace (𝓡 (n + 1)) y,
      mvfderiv (𝓡 (n + 1)) h y v = 0 →
        D.hessian h y v v ≤ H * g.inner y v v)
    (hcomplete : PoincareConjecture.MetricComplete g)
    (hsec : ∀ y (v w : TangentSpace (𝓡 (n + 1)) y),
      -1 ≤ D.sectionalCurvature y v w)
    (p : M) (t : ℝ)
    (hinside : ∀ x : M, f x = t → x ∈ g.ball p 1)
    (hbuffer : ∀ x : M, f x = t →
      {y | g.edist x y ≤ ENNReal.ofReal (80 * r)} ⊆ U) :
    ∃ hreg : ∀ y ∈ U, mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) f y ≠ 0,
      letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
        ⟨finrank_euclideanSpace_fin⟩
      letI := Poincare.Geometry.Manifold.RegularLevel.openLevelSetChartedSpace hf U hreg n t
      letI := Poincare.Geometry.Manifold.RegularLevel.isManifold_openLevelSet hf U hreg n t
      let L := Poincare.Geometry.Manifold.RegularLevel.openLevelSet f U t
      let gL := g.regularLevelMetric hf U hreg t
      let N := ⌈PoincareConjecture.RiemannianMetric.modelVolume (n + 1) 1 3 /
        PoincareConjecture.RiemannianMetric.modelVolume (n + 1) 1 (r / 2)⌉₊
      PoincareConjecture.MetricComplete gL ∧ Finite (ConnectedComponents L) ∧
        Nat.card (ConnectedComponents L) ≤ N ∧
        ∀ x y : L, y ∈ connectedComponent x →
          gL.edist x y ≤ ENNReal.ofReal
            ((N : ℝ) * (18 * r * Real.exp (128 * H * r))) := by
  classical
  have hreg : ∀ y ∈ U, mfderiv (𝓡 (n+1)) 𝓘(ℝ,ℝ) f y ≠ 0 := by
    intro y hy
    exact (g.tangentNorm_gradient_pos_iff f y).mp
      (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2) (hfgrad y hy).1)
  refine ⟨hreg,?_⟩
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n+1))) = n+1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let := openLevelSetChartedSpace hf U hreg n t
  let := isManifold_openLevelSet hf U hreg n t
  let L := openLevelSet f U t
  let incl := openLevelIncl f U t
  let gL := g.regularLevelMetric hf U hreg t
  let N := ⌈RiemannianMetric.modelVolume (n+1) 1 3 /
    RiemannianMetric.modelVolume (n+1) 1 (r/2)⌉₊
  let A := 9*Real.exp (128*H*r)
  let d := 18*r*Real.exp (128*H*r)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hlevelU : f ⁻¹' {t} ⊆ (U : Set M) := by
    intro z hz
    apply hbuffer z hz
    change g.edist z z ≤ ENNReal.ofReal (80*r)
    simp only [RiemannianMetric.edist,Manifold.riemannianEDist_self]
    exact bot_le
  have hemb : Topology.IsClosedEmbedding incl := by
    refine ⟨isEmbedding_openLevelIncl f U t,?_⟩
    rw [range_openLevelIncl]
    rw [inter_eq_right.mpr hlevelU]
    exact isClosed_singleton.preimage hf.continuous
  have hcL : MetricComplete gL :=
    RiemannianMetric.metricComplete_of_isClosedEmbedding gL g
      (contMDiff_openLevelIncl hf U hreg n t) hemb
      (g.regularLevelMetric_inner hf U hreg t) hcomplete
  have hlocal (x y : L) (hxy : (g.edist (incl x) (incl y)).toReal < 2*r) :
      gL.edist x y ≤ ENNReal.ofReal A * g.edist (incl x) (incl y) ∧ Joined x y := by
    obtain ⟨hreg',hlocal'⟩ :=
      D.regularLevel_edist_le_of_opposite_gradients hf hh U hH
        (by positivity : 0<2*r) hfgrad hhgrad hpair hfhess hhhess hcomplete (incl x)
        (by simpa only [show 40*(2*r)=80*r by ring] using hbuffer (incl x) x.2)
    have hself : incl x ∈ g.ball (incl x) (2*r) := by
      simp only [RiemannianMetric.ball,mem_ofPred_eq,RiemannianMetric.edist,
        Manifold.riemannianEDist_self,ENNReal.ofReal_pos]
      positivity
    have hnear : incl y ∈ g.ball (incl x) (2*r) := by
      change g.edist (incl x) (incl y) < ENNReal.ofReal (2*r)
      rw [← ENNReal.ofReal_toReal (g.edist_ne_top (incl x) (incl y))]
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg).mpr hxy
    have he := hlocal' t x y hself hnear
    simpa only [A,show 64*H*(2*r)=128*H*r by ring] using he
  have himage (x : L) : incl x ∈ g.ball p 1 := hinside (incl x) x.2
  obtain ⟨hfinite,hcard⟩ := g.connectedComponents_card_le_of_unitBall_local_connectivity
    p (by omega : 1≤n+1) hr hr1 hcomplete D hsec incl himage
    (fun x y hxy => pathComponent_subset_component y (hlocal x y hxy).2.symm)
  refine ⟨hcL,hfinite,hcard,?_⟩
  intro x y hxy
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : L → Type _) := ⟨gL.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : L → Type _) :=
    ⟨⟨gL.inner,gL.toContinuousRiemannianMetric.continuous,fun _ _ _ => rfl⟩⟩
  let : EMetricSpace L := EMetricSpace.ofRiemannianMetric (𝓡 n) L
  let C := connectedComponent x
  let : ConnectedSpace C := Subtype.connectedSpace isConnected_connectedComponent
  have hCfin : ∀ a b : C, edist a b ≠ ⊤ := Poincare.edist_ne_top_of_preconnected
  let : MetricSpace C := EMetricSpace.toMetricSpace hCfin
  let xC : C := ⟨x,mem_connectedComponent⟩
  let yC : C := ⟨y,hxy⟩
  have hlocalC (a b : C) (hab : (g.edist (incl a.val) (incl b.val)).toReal < 2*r) :
      dist a b ≤ d := by
    have he := (hlocal a.val b.val hab).1
    have hreal : (gL.edist a.val b.val).toReal ≤ A*(g.edist (incl a.val) (incl b.val)).toReal := by
      have ht := ENNReal.toReal_mono
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (g.edist_ne_top _ _)) he
      simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal hA] using ht
    change (gL.edist a.val b.val).toReal ≤ d
    calc
      _ ≤ A*(g.edist (incl a.val) (incl b.val)).toReal := hreal
      _ ≤ A*(2*r) := mul_le_mul_of_nonneg_left hab.le hA
      _ = d := by dsimp [A,d]; ring
  have hdiam := g.dist_le_of_unitBall_cover_and_local_distance_bound
    p (by omega : 1≤n+1) hr hr1 hd hcomplete D hsec
    (fun z : C => incl z.val) (fun z => himage z.val) hlocalC xC yC
  have hreal : (gL.edist x y).toReal ≤ (N:ℝ)*d := hdiam
  have hne : gL.edist x y ≠ ⊤ := hCfin xC yC
  rw [← ENNReal.ofReal_toReal hne]
  exact ENNReal.ofReal_le_ofReal hreal
