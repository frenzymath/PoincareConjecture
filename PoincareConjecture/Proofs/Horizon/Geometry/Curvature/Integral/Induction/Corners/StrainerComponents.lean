import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.LocalDistance
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.AnnularVolume
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.Components
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.Diameter
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open Poincare.Geometry.Manifold.RegularFiber
open scoped Manifold ContDiff Topology Bundle


theorem PoincareConjecture.RiemannianMetric.strainer_openFiber_components_and_diameter
    {m k : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [PreconnectedSpace M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + k))) M]
    [IsManifold (𝓡 (m + k)) ∞ M]
    (g : PoincareConjecture.RiemannianMetric (m + k) M) (D : PoincareConjecture.LeviCivitaData g) (hc : PoincareConjecture.MetricComplete g)
    (hn : 1 ≤ m+k)
    (hsec : ∀ x (v w : TangentSpace (𝓡 (m+k)) x), -1 ≤ D.sectionalCurvature x v w)
    (f h : Fin k → M → ℝ)
    (hf : ∀ i, ContMDiff (𝓡 (m + k)) 𝓘(ℝ, ℝ) ∞ (f i))
    (hh : ∀ i, ContMDiff (𝓡 (m + k)) 𝓘(ℝ, ℝ) ∞ (h i))
    (U : Opens M) {δ C : ℝ} (hδ : 0 ≤ δ)
    (hsmall : δ ≤ 1 / (256 * ((k : ℝ) + 1) ^ 2)) (hC : 0 ≤ C)
    (hunit : ∀ x ∈ U, ∀ i,
      g.tangentNorm x (g.gradient (f i) x) ≤ 1 ∧
      g.tangentNorm x (g.gradient (h i) x) ≤ 1)
    (hopposite : ∀ x ∈ U, ∀ i,
      g.inner x (g.gradient (f i) x) (g.gradient (h i) x) ≤ -1 + 2 * δ)
    (hcross : ∀ x ∈ U, ∀ i j, i ≠ j →
      |g.inner x (g.gradient (f i) x) (g.gradient (f j) x)| ≤ δ ∧
      |g.inner x (g.gradient (h i) x) (g.gradient (f j) x)| ≤ δ)
    (htight : ∀ x ∈ U, ∀ i j, i ≠ j →
      g.inner x (g.gradient (f i) x) (g.gradient (f j) x) ≤ 0)
    (hH : ∀ x ∈ U, ∀ i w,
      D.hessian (f i) x w w ≤ C * g.inner x w w ∧
      D.hessian (h i) x w w ≤ C * g.inner x w w) (p : M) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    let A := 9 * Real.exp (128*C*r)
    let q := r / (4*A^k)
    let N := ⌈PoincareConjecture.RiemannianMetric.modelVolume (m+k) 1 3 /
      PoincareConjecture.RiemannianMetric.modelVolume (m+k) 1 (q/2)⌉₊
    let F := fun y i => f i y
    let hF : ContMDiff (𝓡 (m+k)) 𝓘(ℝ, Fin k → ℝ) ∞ F :=
      contMDiff_pi_space.mpr hf
    ∃ hreg : ∀ x ∈ U, Surjective (mfderiv (𝓡 (m+k)) 𝓘(ℝ, Fin k → ℝ) F x),
      ∀ c : Fin k → ℝ,
        (∀ x ∈ U, F x = c → x ∈ g.ball p 1) →
        (∀ x ∈ U, F x = c → ∀ z,
          g.edist x z ≤ ENNReal.ofReal (40*r) → z ∈ U) →
        letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+k))) = m+k) :=
          ⟨finrank_euclideanSpace_fin⟩
        letI := openFiberChartedSpace (m := m) hF U hreg c
        letI := isManifold_openFiber (m := m) hF U hreg c
        let L := openFiber F U c
        let gL := g.openRegularFiberMetric hF U hreg c
        IsCompact (Set.univ : Set L) ∧ PoincareConjecture.MetricComplete gL ∧
          Finite (ConnectedComponents L) ∧ Nat.card (ConnectedComponents L) ≤ N ∧
          ∀ x y : L, y ∈ connectedComponent x →
            gL.edist x y ≤ ENNReal.ofReal ((N:ℝ)*r/2) := by
  classical
  let F := fun y i => f i y
  let hF : ContMDiff (𝓡 (m+k)) 𝓘(ℝ,Fin k → ℝ) ∞ F := contMDiff_pi_space.mpr hf
  let A := 9*Real.exp (128*C*r)
  let q := r/(4*A^k)
  let N := ⌈PoincareConjecture.RiemannianMetric.modelVolume (m+k) 1 3 /
    PoincareConjecture.RiemannianMetric.modelVolume (m+k) 1 (q/2)⌉₊
  have hA1 : 1 ≤ A := by
    have he := Real.one_le_exp (show 0≤128*C*r by positivity)
    dsimp only [A]
    linarith
  have hAp : 0 < A^k := pow_pos (by linarith) _
  have hAk1 : 1 ≤ A^k := one_le_pow₀ hA1
  have hq : 0 < q := by dsimp [q]; positivity
  have hq1 : q ≤ 1 := by
    apply (div_le_one (by positivity : 0<4*A^k)).mpr
    linarith
  have hscale : A^k*(2*q) = r/2 := by
    dsimp only [q]
    field_simp
    ring
  obtain ⟨hreg, hlocal⟩ := g.strainer_openFiber_edist_le_of_ambient_closedBall D hc
    f h hf hh U hδ hsmall hC hunit hopposite hcross htight hH hr
  have hsmall' : δ ≤ 1/(8*((k:ℝ)+1)) := hsmall.trans
    (one_div_le_one_div_of_le (by positivity) (by
      have hk : 0 ≤ (k:ℝ) := Nat.cast_nonneg k
      nlinarith [sq_nonneg (k:ℝ)]))
  obtain ⟨hreg', hcompactAll⟩ := g.strainer_openFiber_total_volume_le_annular_mul_pow
    D hc hsec f (fun x i => g.gradient (h i) x) hf U hδ hsmall'
    (show 0≤C/2 by positivity) hunit hopposite (fun x hx i j hij => (hcross x hx i j hij).1)
    htight (fun x hx i w => by simpa using (hH x hx i w).1)
    p (show (0:ℝ)<1/2 by norm_num) (show (1/2:ℝ)≤1 by norm_num)
    (show 0<80*r by positivity)
  refine ⟨hreg, ?_⟩
  intro c hinside hbuffer
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+k))) = m+k) :=
    ⟨finrank_euclideanSpace_fin⟩
  let := openFiberChartedSpace (m := m) hF U hreg c
  let := isManifold_openFiber (m := m) hF U hreg c
  let L := openFiber F U c
  let incl := openFiberIncl F U c
  let gL := g.openRegularFiberMetric hF U hreg c
  have hcompact : IsCompact (Set.univ : Set L) := (hcompactAll c
    (fun x hx hfx => by
      simpa only [show (2:ℝ)*(1/2)=1 by norm_num] using
        (show g.edist p x < ENNReal.ofReal 1 from hinside x hx hfx))
    (fun x hx hfx y hy => hbuffer x hx hfx y (by
      simpa only [show 80*r*(1/2)=40*r by ring] using hy))).1
  let : CompactSpace L := isCompact_univ_iff.mp hcompact
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 m) : L → Type _) :=
    ⟨gL.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin m))
      (TangentSpace (𝓡 m) : L → Type _) :=
    ⟨⟨gL.inner,gL.toContinuousRiemannianMetric.continuous,fun _ _ _ => rfl⟩⟩
  let : EMetricSpace L := EMetricSpace.ofRiemannianMetric (𝓡 m) L
  have hcompleteL : PoincareConjecture.MetricComplete gL := by
    change CompleteSpace L
    infer_instance
  have hloc (x y : L) (hxy : (g.edist (incl x) (incl y)).toReal < 2*q) :
      gL.edist x y ≤ ENNReal.ofReal (r/2) ∧ Joined x y := by
    have hprod : A^k*(g.edist (incl x) (incl y)).toReal < r/2 := by
      rw [← hscale]
      exact mul_lt_mul_of_pos_left hxy hAp
    have hbound : ENNReal.ofReal (A^k) * g.edist (incl x) (incl y) ≤
        ENNReal.ofReal (r/2) := by
      rw [← ENNReal.ofReal_toReal (g.edist_ne_top _ _), ← ENNReal.ofReal_mul hAp.le]
      exact ENNReal.ofReal_le_ofReal hprod.le
    have hgap : ENNReal.ofReal (A^k) * g.edist (incl x) (incl y) < ENNReal.ofReal r :=
      hbound.trans_lt ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mpr (by linarith))
    have he := hlocal c x y (hbuffer _ x.1.2 x.2) hgap
    exact ⟨he.1.trans hbound, he.2⟩
  have himage (x : L) : incl x ∈ g.ball p 1 := hinside _ x.1.2 x.2
  obtain ⟨hfinite,hcard⟩ := g.connectedComponents_card_le_of_unitBall_local_connectivity
    p hn hq hq1 hc D hsec incl himage
    (fun x y hxy => pathComponent_subset_component y (hloc x y hxy).2.symm)
  refine ⟨hcompact,hcompleteL,hfinite,hcard,?_⟩
  intro x y hxy
  let E := connectedComponent x
  let : ConnectedSpace E := Subtype.connectedSpace isConnected_connectedComponent
  have hEfin : ∀ a b : E, EDist.edist a b ≠ ⊤ := Poincare.edist_ne_top_of_preconnected
  let : MetricSpace E := EMetricSpace.toMetricSpace hEfin
  let xE : E := ⟨x,mem_connectedComponent⟩
  let yE : E := ⟨y,hxy⟩
  have hlocalE (a b : E) (hab : (g.edist (incl a.val) (incl b.val)).toReal < 2*q) :
      dist a b ≤ r/2 := by
    have he := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hloc a.val b.val hab).1
    change (gL.edist a.val b.val).toReal ≤ r/2
    simpa only [ENNReal.toReal_ofReal (by positivity : 0≤r/2)] using he
  have hdiam := g.dist_le_of_unitBall_cover_and_local_distance_bound p hn hq hq1
    (show 0≤r/2 by positivity) hc D hsec (fun z : E => incl z.val)
    (fun z => himage z.val) hlocalE xE yE
  have hreal' : (gL.edist x y).toReal ≤ (N:ℝ)*(r/2) := hdiam
  have hreal : (gL.edist x y).toReal ≤ (N:ℝ)*r/2 := by
    simpa only [mul_div_assoc] using hreal'
  have hne : gL.edist x y ≠ ⊤ := hEfin xE yE
  rw [← ENNReal.ofReal_toReal hne]
  exact ENNReal.ofReal_le_ofReal hreal
