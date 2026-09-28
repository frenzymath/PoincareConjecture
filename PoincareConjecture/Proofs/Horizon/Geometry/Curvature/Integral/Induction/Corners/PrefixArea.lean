import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.AnnularVolume
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.PrefixVolume
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.PrefixBounds
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Coarea.Variation.Area

open Set Function TopologicalSpace MeasureTheory
open Poincare.Geometry.Manifold.RegularFiber Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Bundle Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
private theorem PoincareConjecture.RiemannianMetric.strainer_total_volume_any_dimension
    {n m k : ℕ} (hdim : n = m + k) {M : Type*} [TopologicalSpace M] [T3Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    (g : PoincareConjecture.RiemannianMetric n M)
    (D : PoincareConjecture.LeviCivitaData g) (hc : PoincareConjecture.MetricComplete g)
    (hsec : ∀ x (v w : TangentSpace (𝓡 n) x), -1 ≤ D.sectionalCurvature x v w)
    (f : Fin k → M → ℝ)
    (w : ∀ x : M, Fin k → TangentSpace (𝓡 n) x)
    (hf : ∀ i, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f i))
    (U : Opens M) {δ H η r : ℝ} (hδ : 0 ≤ δ)
    (hsmall : δ ≤ 1 / (8 * ((k : ℝ) + 1))) (hHnonneg : 0 ≤ H)
    (hunit : ∀ x ∈ U, ∀ i, g.tangentNorm x (g.gradient (f i) x) ≤ 1 ∧
      g.tangentNorm x (w x i) ≤ 1)
    (hopposite : ∀ x ∈ U, ∀ i,
      g.inner x (g.gradient (f i) x) (w x i) ≤ -1 + 2 * δ)
    (hcross : ∀ x ∈ U, ∀ i j, i ≠ j →
      |g.inner x (g.gradient (f i) x) (g.gradient (f j) x)| ≤ δ)
    (htight : ∀ x ∈ U, ∀ i j, i ≠ j →
      g.inner x (g.gradient (f i) x) (g.gradient (f j) x) ≤ 0)
    (hH : ∀ x ∈ U, ∀ i v, D.hessian (f i) x v v ≤ (H / r) * g.inner x v v)
    (p : M) (hr : 0 < r) (hr1 : r ≤ 1) (hη : 0 < η) :
    let F := fun y i => f i y
    let hF : ContMDiff (𝓡 n) 𝓘(ℝ, Fin k → ℝ) ∞ F :=
      contMDiff_pi_space.mpr hf
    ∃ hreg : ∀ x ∈ U, Surjective
        (mfderiv (𝓡 n) 𝓘(ℝ, Fin k → ℝ) F x),
      ∀ c : Fin k → ℝ,
        (∀ x ∈ U, F x = c → g.edist p x < ENNReal.ofReal (2 * r)) →
        (∀ x ∈ U, F x = c → ∀ y,
          g.edist x y ≤ ENNReal.ofReal (η * r) → y ∈ U) →
        letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = m + k) :=
          ⟨by rw [finrank_euclideanSpace_fin, hdim]⟩
        letI := openFiberChartedSpace (m := m) hF U hreg c
        letI := isManifold_openFiber (m := m) hF U hreg c
        let gL := PoincareConjecture.RiemannianMetric.Induced.pullbackMetric g
          (openFiberIncl F U c) (contMDiff_openFiberIncl (m := m) hF U hreg c)
          (injective_mfderiv_openFiberIncl (m := m) hF U hreg c)
        IsCompact (Set.univ : Set (openFiber F U c)) ∧
          (PoincareConjecture.RiemannianMetric.volumeMeasure gL).real Set.univ ≤
            PoincareConjecture.RiemannianMetric.annularCornerVolumeConstant m k H η * r ^ m := by
  subst n
  exact g.strainer_openFiber_total_volume_le_annular_mul_pow D hc hsec
    f w hf U hδ hsmall hHnonneg hunit hopposite hcross htight hH p hr hr1 hη
private theorem regularLevelArea_eq_top_volume
    {d : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (d + 1))) M] [IsManifold (𝓡 (d + 1)) ∞ M]
    (g : PoincareConjecture.RiemannianMetric (d + 1) M) {φ : M → ℝ}
    (hφ : ContMDiff (𝓡 (d + 1)) 𝓘(ℝ, ℝ) ∞ φ)
    (hreg : ∀ x, mfderiv (𝓡 (d + 1)) 𝓘(ℝ, ℝ) φ x ≠ 0) (t : ℝ) :
    g.regularLevelArea hφ t =
      (g.regularLevelVolume hφ ⊤ (fun x _ => hreg x) t).real univ := by
  have htop : g.regularDomain hφ = ⊤ := by
    apply top_le_iff.mp
    intro x _
    exact (g.mem_regularDomain_iff hφ x).mpr (hreg x)
  unfold PoincareConjecture.RiemannianMetric.regularLevelArea
  have hcongr (U V : Opens M)
      (hU : ∀ x ∈ U, mfderiv (𝓡 (d + 1)) 𝓘(ℝ, ℝ) φ x ≠ 0)
      (hV : ∀ x ∈ V, mfderiv (𝓡 (d + 1)) 𝓘(ℝ, ℝ) φ x ≠ 0)
      (he : U = V) :
      (g.regularLevelVolume hφ U hU t).real univ =
        (g.regularLevelVolume hφ V hV t).real univ := by
    cases he
    rfl
  exact hcongr _ _ _ _ htop

theorem PoincareConjecture.RiemannianMetric.strainer_prefix_regularLevelArea_le_annular_mul_pow
    {d k : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin ((d + 1) + k))) M]
    [IsManifold (𝓡 ((d + 1) + k)) ∞ M]
    (g : PoincareConjecture.RiemannianMetric ((d + 1) + k) M)
    (D : PoincareConjecture.LeviCivitaData g) (hc : PoincareConjecture.MetricComplete g)
    (hsec : ∀ x (v w : TangentSpace (𝓡 ((d + 1) + k)) x),
      -1 ≤ D.sectionalCurvature x v w)
    (f : Fin (k + 1) → M → ℝ)
    (w : ∀ x : M, Fin (k + 1) → TangentSpace (𝓡 ((d + 1) + k)) x)
    (hf : ∀ i, ContMDiff (𝓡 ((d + 1) + k)) 𝓘(ℝ, ℝ) ∞ (f i))
    (U : Opens M) {δ H η r : ℝ} (hδ : 0 ≤ δ)
    (hsmall : δ ≤ 1 / (8 * ((k : ℝ) + 2))) (hHnonneg : 0 ≤ H)
    (hunit : ∀ x ∈ U, ∀ i, g.tangentNorm x (g.gradient (f i) x) ≤ 1 ∧
      g.tangentNorm x (w x i) ≤ 1)
    (hopposite : ∀ x ∈ U, ∀ i,
      g.inner x (g.gradient (f i) x) (w x i) ≤ -1 + 2 * δ)
    (hcross : ∀ x ∈ U, ∀ i j, i ≠ j →
      |g.inner x (g.gradient (f i) x) (g.gradient (f j) x)| ≤ δ)
    (htight : ∀ x ∈ U, ∀ i j, i ≠ j →
      g.inner x (g.gradient (f i) x) (g.gradient (f j) x) ≤ 0)
    (hH : ∀ x ∈ U, ∀ i v, D.hessian (f i) x v v ≤ (H / r) * g.inner x v v)
    (p : M) (hr : 0 < r) (hr1 : r ≤ 1) (hη : 0 < η) :
    let P := fun y (i : Fin k) => f i.castSucc y
    let hP : ContMDiff (𝓡 ((d + 1) + k)) 𝓘(ℝ, Fin k → ℝ) ∞ P :=
      contMDiff_pi_space.mpr (fun i => hf i.castSucc)
    ∃ hprefix : ∀ x ∈ U, Surjective
        (mfderiv (𝓡 ((d + 1) + k)) 𝓘(ℝ, Fin k → ℝ) P x),
      ∀ c : Fin k → ℝ,
        letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin ((d + 1) + k))) =
          (d + 1) + k) := ⟨finrank_euclideanSpace_fin⟩
        letI := openFiberChartedSpace (m := d + 1) hP U hprefix c
        letI := isManifold_openFiber (m := d + 1) hP U hprefix c
        let gP := g.openRegularFiberMetric hP U hprefix c
        let φP := f (Fin.last k) ∘ openFiberIncl P U c
        ∃ hφP : ContMDiff (𝓡 (d + 1)) 𝓘(ℝ, ℝ) ∞ φP,
          (∀ x : openFiber P U c,
            (1 / 2 ≤ gP.tangentNorm x (gP.gradient φP x) ∧
              gP.tangentNorm x (gP.gradient φP x) ≤ 1) ∧
            ∀ v : TangentSpace (𝓡 (d + 1)) x,
              gP.leviCivitaData.hessian φP x v v ≤ (2 * H / r) * gP.inner x v v) ∧
          ∀ t : ℝ,
            (∀ x ∈ U, P x = c → f (Fin.last k) x = t →
              g.edist p x < ENNReal.ofReal (2 * r)) →
            (∀ x ∈ U, P x = c → f (Fin.last k) x = t → ∀ y,
              g.edist x y ≤ ENNReal.ofReal (η * r) → y ∈ U) →
            gP.regularLevelArea hφP t ≤
              PoincareConjecture.RiemannianMetric.annularCornerVolumeConstant d (k + 1) H η * r ^ d := by
  classical
  let P := fun y (i : Fin k) => f i.castSucc y
  let hP : ContMDiff (𝓡 ((d + 1) + k)) 𝓘(ℝ, Fin k → ℝ) ∞ P :=
    contMDiff_pi_space.mpr (fun i => hf i.castSucc)
  have hsmall' : δ ≤ 1 / (8 * ((k : ℝ) + 1)) := hsmall.trans
    (one_div_le_one_div_of_le (by positivity) (by linarith))
  obtain ⟨_, hprefix, hbounds⟩ := g.strainer_prefix_openFiber_bounds D f w hf U
    hδ hsmall' (div_nonneg hHnonneg hr.le) hunit hopposite hcross htight hH
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin ((d + 1) + k))) =
    (d + 1) + k) := ⟨finrank_euclideanSpace_fin⟩
  let (c : Fin k → ℝ) := openFiberChartedSpace (m := d + 1) hP U hprefix c
  let (c : Fin k → ℝ) := isManifold_openFiber (m := d + 1) hP U hprefix c
  have hlast : ∀ c : Fin k → ℝ, ∀ x : openFiber P U c,
      mfderiv (𝓡 (d + 1)) 𝓘(ℝ, ℝ)
        (f (Fin.last k) ∘ openFiberIncl P U c) x ≠ 0 := by
    intro c x hx
    let gP := g.openRegularFiberMetric hP U hprefix c
    have hz := (gP.gradient_eq_zero_iff_mfderiv_eq_zero _ x).mpr hx
    have hb := ((hbounds c).2 x).1.1
    rw [hz] at hb
    simp only [PoincareConjecture.RiemannianMetric.tangentNorm, map_zero, Real.sqrt_zero] at hb
    norm_num at hb
  obtain ⟨hfull, hvol⟩ := g.exists_prefix_fiber_volume_identity f hf U hprefix hlast
  obtain ⟨hfull', harea⟩ := g.strainer_total_volume_any_dimension
    (m := d) (k := k + 1) (by omega) D hc hsec f w hf U
    hδ (by simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using hsmall)
    hHnonneg hunit hopposite hcross htight hH p hr hr1 hη
  refine ⟨hprefix, ?_⟩
  intro c
  let gP := g.openRegularFiberMetric hP U hprefix c
  let φP := f (Fin.last k) ∘ openFiberIncl P U c
  let hφP := (hf (Fin.last k)).comp
    (contMDiff_openFiberIncl (m := d + 1) hP U hprefix c)
  refine ⟨hφP, ?_, ?_⟩
  · intro x
    refine ⟨((hbounds c).2 x).1, ?_⟩
    intro v
    simpa only [mul_div_assoc] using ((hbounds c).2 x).2 v
  · intro t hbounded hbuffer
    let cfull : Fin (k + 1) → ℝ := Fin.lastCases t c
    have hcpre : (fun i : Fin k => cfull i.castSucc) = c := by
      funext i
      simp [cfull]
    have hclast : cfull (Fin.last k) = t := by simp [cfull]
    have hfpre (x : M) (hx : (fun i => f i x) = cfull) : P x = c := by
      funext i
      simpa only [P, cfull, Fin.lastCases_castSucc] using congrFun hx i.castSucc
    have hflast (x : M) (hx : (fun i => f i x) = cfull) : f (Fin.last k) x = t := by
      simpa only [hclast] using congrFun hx (Fin.last k)
    have hb := (harea cfull
      (fun x hx he => hbounded x hx (hfpre x he) (hflast x he))
      (fun x hx he => hbuffer x hx (hfpre x he) (hflast x he))).2
    obtain ⟨hlevel, hvolc⟩ := hvol cfull
    have he := hvolc univ
    simp only [Set.mem_univ, Set.ofPred_true] at he
    have hearea := regularLevelArea_eq_top_volume
      (g.openRegularFiberMetric hP U hprefix (fun i => cfull i.castSucc))
      ((hf (Fin.last k)).comp
        (contMDiff_openFiberIncl (m := d + 1) hP U hprefix (fun i => cfull i.castSucc)))
      hlevel (cfull (Fin.last k))
    have hfinal := (hearea.trans he).trans_le hb
    let area (c' : Fin k → ℝ) (t' : ℝ) : ℝ :=
      (g.openRegularFiberMetric hP U hprefix c').regularLevelArea
        ((hf (Fin.last k)).comp
          (contMDiff_openFiberIncl (m := d + 1) hP U hprefix c')) t'
    change area (fun i => cfull i.castSucc) (cfull (Fin.last k)) ≤ _ at hfinal
    rw [hcpre, hclast] at hfinal
    exact hfinal
