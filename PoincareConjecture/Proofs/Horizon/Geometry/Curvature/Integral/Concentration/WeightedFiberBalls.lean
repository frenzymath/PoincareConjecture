import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.WeightedFiberScaling
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Scaling.Volume







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace MeasureTheory
open Poincare.Geometry.Manifold.RegularFiber
open scoped Manifold ContDiff Topology


noncomputable def PoincareConjecture.RiemannianMetric.openFiberWeightedAmbientBallRatio
    {m k : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m+k))) M] [IsManifold (𝓡 (m+k)) ∞ M]
    (g : PoincareConjecture.RiemannianMetric (m+k) M)
    {f : M → Fin k → ℝ} (hf : ContMDiff (𝓡 (m+k)) 𝓘(ℝ,Fin k → ℝ) ∞ f)
    (U : TopologicalSpace.Opens M)
    (hreg : ∀ x ∈ U, Function.Surjective
      (mfderiv (𝓡 (m+k)) 𝓘(ℝ,Fin k → ℝ) f x))
    (v : Fin k → ℝ) (K : openFiber f U v → ℝ) (p : M) (r R : ℝ) : ℝ :=
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+k))) = m+k) :=
    ⟨finrank_euclideanSpace_fin⟩
  letI := openFiberChartedSpace (m := m) hf U hreg v
  letI := isManifold_openFiber (m := m) hf U hreg v
  let gFiber := PoincareConjecture.RiemannianMetric.openRegularFiberMetric hf U hreg v g
  (∫ x in {x | openFiberIncl f U v x ∈ g.ball p r},
    max 0 (gFiber.leviCivitaData.scalarCurvature x) ∂gFiber.volumeMeasure) /
      (1 + ∫ x in {x | openFiberIncl f U v x ∈ g.ball p R}, K x ∂gFiber.volumeMeasure)



theorem PoincareConjecture.RiemannianMetric.image_preimage_ball_rescaledMetric
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : PoincareConjecture.RiemannianMetric n M) {a : ℝ} (ha : 0 < a)
    {X Y : Type*} (e : X ≃ Y) (iX : X → M) (iY : Y → M)
    (hinc : ∀ x, iY (e x) = iX x) (p : M) (r : ℝ) :
    e '' (iX ⁻¹' g.ball p r) =
      iY ⁻¹' (PoincareConjecture.rescaledMetric g a ha).ball p (Real.sqrt a * r) := by
  rw [PoincareConjecture.rescaledMetric_ball,
    mul_div_cancel_left₀ r (Real.sqrt_pos.mpr ha).ne']
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change iY (e x) ∈ g.ball p r
    rw [hinc]
    exact hx
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    change iX (e.symm y) ∈ g.ball p r
    rw [← hinc, e.apply_symm_apply]
    exact hy

theorem PoincareConjecture.RiemannianMetric.exists_scaled_openFiber_weighted_ambientBall_equivalence
    {m k : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m+k))) M]
    [IsManifold (𝓡 (m+k)) ∞ M]
    (g : PoincareConjecture.RiemannianMetric (m+k) M)
    {f : M → Fin k → ℝ} (hf : ContMDiff (𝓡 (m+k)) 𝓘(ℝ,Fin k → ℝ) ∞ f)
    (U : TopologicalSpace.Opens M)
    (hreg : ∀ x ∈ U, Function.Surjective
      (mfderiv (𝓡 (m+k)) 𝓘(ℝ,Fin k → ℝ) f x))
    (v : Fin k → ℝ) (hm : 2 ≤ m) {a : ℝ} (ha : 1 ≤ a) :
    let F := fun x => Real.sqrt a • f x
    let w := Real.sqrt a • v
    ∃ hF : ContMDiff (𝓡 (m+k)) 𝓘(ℝ,Fin k → ℝ) ∞ F,
      ∃ hregF : ∀ x ∈ U, Function.Surjective
        (mfderiv (𝓡 (m+k)) 𝓘(ℝ,Fin k → ℝ) F x),
        letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+k))) = m+k) :=
          ⟨finrank_euclideanSpace_fin⟩
        letI := openFiberChartedSpace (m := m) hf U hreg v
        letI := isManifold_openFiber (m := m) hf U hreg v
        letI := openFiberChartedSpace (m := m) hF U hregF w
        letI := isManifold_openFiber (m := m) hF U hregF w
        let gOld := PoincareConjecture.RiemannianMetric.openRegularFiberMetric hf U hreg v g
        let gNew := PoincareConjecture.RiemannianMetric.openRegularFiberMetric hF U hregF w
          (PoincareConjecture.rescaledMetric g a (zero_lt_one.trans_le ha))
        ∃ e : openFiber f U v ≃ₘ⟮𝓡 m,𝓡 m⟯ openFiber F U w,
          (∀ x, openFiberIncl F U w (e x) = openFiberIncl f U v x) ∧
          (∀ (x : openFiber f U v) (z z' : TangentSpace (𝓡 m) x),
            gNew.inner (e x) (mfderiv (𝓡 m) (𝓡 m) e x z)
              (mfderiv (𝓡 m) (𝓡 m) e x z') = a * gOld.inner x z z') ∧
          (∀ x y, PoincareConjecture.RiemannianMetric.edist gNew (e x) (e y) =
            ENNReal.ofReal (Real.sqrt a) * gOld.edist x y) ∧
          (PoincareConjecture.MetricComplete g → f ⁻¹' {v} ⊆ U →
            PoincareConjecture.MetricComplete gOld ∧ PoincareConjecture.MetricComplete gNew) ∧
          (∀ (p : M) (r : ℝ),
            e '' {x | openFiberIncl f U v x ∈ g.ball p r} =
              {y | openFiberIncl F U w y ∈
                (PoincareConjecture.rescaledMetric g a (zero_lt_one.trans_le ha)).ball p
                  (Real.sqrt a * r)}) ∧
          ∀ (K : openFiber f U v → ℝ), (∀ x, 0 ≤ K x) →
            ∀ (p : M) (r R : ℝ),
              ((∫ x in {x | openFiberIncl f U v x ∈ g.ball p r},
                  max 0 (gOld.leviCivitaData.scalarCurvature x) ∂gOld.volumeMeasure) /
                (1 + ∫ x in {x | openFiberIncl f U v x ∈ g.ball p R},
                  K x ∂gOld.volumeMeasure)) ≤
              ((∫ y in {y | openFiberIncl F U w y ∈
                  (PoincareConjecture.rescaledMetric g a (zero_lt_one.trans_le ha)).ball p
                    (Real.sqrt a * r)},
                  max 0 (gNew.leviCivitaData.scalarCurvature y) ∂gNew.volumeMeasure) /
                (1 + ∫ y in {y | openFiberIncl F U w y ∈
                    (PoincareConjecture.rescaledMetric g a (zero_lt_one.trans_le ha)).ball p
                      (Real.sqrt a * R)},
                  a⁻¹ * K (e.symm y) ∂gNew.volumeMeasure)) := by
  let F := fun x => Real.sqrt a • f x
  let w := Real.sqrt a • v
  obtain ⟨hF, hregF, hdata⟩ :=
    g.exists_scaled_openFiber_weighted_integral_equivalence hf U hreg v hm ha
  refine ⟨hF, hregF, ?_⟩
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+k))) = m+k) :=
    ⟨finrank_euclideanSpace_fin⟩
  let := openFiberChartedSpace (m := m) hf U hreg v
  let := isManifold_openFiber (m := m) hf U hreg v
  let := openFiberChartedSpace (m := m) hF U hregF w
  let := isManifold_openFiber (m := m) hF U hregF w
  let gOld := PoincareConjecture.RiemannianMetric.openRegularFiberMetric hf U hreg v g
  let gNew := PoincareConjecture.RiemannianMetric.openRegularFiberMetric hF U hregF w
    (PoincareConjecture.rescaledMetric g a (zero_lt_one.trans_le ha))
  obtain ⟨e, hinc, hmetric, hdist, hcomplete, hratio⟩ := hdata
  have himage (p : M) (r : ℝ) :
      e '' {x | openFiberIncl f U v x ∈ g.ball p r} =
        {y | openFiberIncl F U w y ∈
          (PoincareConjecture.rescaledMetric g a (zero_lt_one.trans_le ha)).ball p
            (Real.sqrt a * r)} :=
    g.image_preimage_ball_rescaledMetric (zero_lt_one.trans_le ha) e.toEquiv
      (openFiberIncl f U v) (openFiberIncl F U w) hinc p r
  refine ⟨e, hinc, hmetric, hdist, hcomplete, himage, ?_⟩
  intro K hK p r R
  rw [← himage p r, ← himage p R]
  exact hratio K hK _ _



theorem PoincareConjecture.RiemannianMetric.exists_scaled_openFiber_ambientBall_divergence
    {m k : ℕ} {M : ℕ → Type*}
    [∀ j, TopologicalSpace (M j)] [∀ j, T3Space (M j)]
    [∀ j, MeasurableSpace (M j)] [∀ j, BorelSpace (M j)]
    [∀ j, ChartedSpace (EuclideanSpace ℝ (Fin (m+k))) (M j)]
    [∀ j, IsManifold (𝓡 (m+k)) ∞ (M j)]
    (g : ∀ j, PoincareConjecture.RiemannianMetric (m+k) (M j))
    (f : ∀ j, M j → Fin k → ℝ)
    (hf : ∀ j, ContMDiff (𝓡 (m+k)) 𝓘(ℝ,Fin k → ℝ) ∞ (f j))
    (U : ∀ j, TopologicalSpace.Opens (M j))
    (hreg : ∀ j x, x ∈ U j → Function.Surjective
      (mfderiv (𝓡 (m+k)) 𝓘(ℝ,Fin k → ℝ) (f j) x))
    (v : ℕ → Fin k → ℝ) (hm : 2 ≤ m)
    (p : ∀ j, M j) (r : ℕ → ℝ) (b : ℝ)
    (hr : ∀ j, 0 < r j) (hr1 : ∀ᶠ j in Filter.atTop, r j ≤ 1)
    (K : ∀ j, openFiber (f j) (U j) (v j) → ℝ) (hK : ∀ j x, 0 ≤ K j x) :
    Filter.Tendsto (fun j => (g j).openFiberWeightedAmbientBallRatio (m := m)
      (hf j) (U j) (hreg j) (v j) (K j) (p j) (r j) (b * r j))
      Filter.atTop Filter.atTop →
    let a := fun j => (r j ^ (2 : ℕ))⁻¹
    let F := fun j x => Real.sqrt (a j) • f j x
    let w := fun j => Real.sqrt (a j) • v j
    let G := fun j => PoincareConjecture.rescaledMetric (g j) (a j)
      (inv_pos.mpr (sq_pos_of_pos (hr j)))
    ∃ hF : ∀ j, ContMDiff (𝓡 (m+k)) 𝓘(ℝ,Fin k → ℝ) ∞ (F j),
      ∃ hregF : ∀ j x, x ∈ U j → Function.Surjective
        (mfderiv (𝓡 (m+k)) 𝓘(ℝ,Fin k → ℝ) (F j) x),
        letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+k))) = m+k) :=
          ⟨finrank_euclideanSpace_fin⟩
        letI : ∀ j, ChartedSpace (EuclideanSpace ℝ (Fin m))
            (openFiber (f j) (U j) (v j)) :=
          fun j => openFiberChartedSpace (m := m) (hf j) (U j) (hreg j) (v j)
        letI : ∀ j, IsManifold (𝓡 m) ∞ (openFiber (f j) (U j) (v j)) :=
          fun j => isManifold_openFiber (m := m) (hf j) (U j) (hreg j) (v j)
        letI : ∀ j, ChartedSpace (EuclideanSpace ℝ (Fin m))
            (openFiber (F j) (U j) (w j)) :=
          fun j => openFiberChartedSpace (m := m) (hF j) (U j) (hregF j) (w j)
        letI : ∀ j, IsManifold (𝓡 m) ∞ (openFiber (F j) (U j) (w j)) :=
          fun j => isManifold_openFiber (m := m) (hF j) (U j) (hregF j) (w j)
        let gOld := fun j => PoincareConjecture.RiemannianMetric.openRegularFiberMetric
          (hf j) (U j) (hreg j) (v j) (g j)
        let gNew := fun j => PoincareConjecture.RiemannianMetric.openRegularFiberMetric
          (hF j) (U j) (hregF j) (w j) (G j)
        ∃ e : ∀ j, openFiber (f j) (U j) (v j) ≃ₘ⟮𝓡 m,𝓡 m⟯
            openFiber (F j) (U j) (w j),
          ∃ Knew : ∀ j, openFiber (F j) (U j) (w j) → ℝ,
          (∀ j x, openFiberIncl (F j) (U j) (w j) (e j x) =
            openFiberIncl (f j) (U j) (v j) x) ∧
          (∀ j (x : openFiber (f j) (U j) (v j)) (z z' : TangentSpace (𝓡 m) x),
            (gNew j).inner (e j x) (mfderiv (𝓡 m) (𝓡 m) (e j) x z)
              (mfderiv (𝓡 m) (𝓡 m) (e j) x z') = a j * (gOld j).inner x z z') ∧
          (∀ j y, Knew j y = r j ^ (2 : ℕ) * K j ((e j).toEquiv.symm y)) ∧
          Filter.Tendsto (fun j => (G j).openFiberWeightedAmbientBallRatio (m := m)
            (hF j) (U j) (hregF j) (w j)
            (Knew j) (p j) 1 b)
            Filter.atTop Filter.atTop := by
  classical
  intro hdiv
  let a := fun j => (r j ^ (2 : ℕ))⁻¹
  let F := fun j x => Real.sqrt (a j) • f j x
  let w := fun j => Real.sqrt (a j) • v j
  let G := fun j => PoincareConjecture.rescaledMetric (g j) (a j)
    (inv_pos.mpr (sq_pos_of_pos (hr j)))
  choose hF hregF hdata using fun j =>
    (g j).exists_scaled_openFiber_metric_equivalence (hf j) (U j) (hreg j) (v j)
      (inv_pos.mpr (sq_pos_of_pos (hr j)))
  refine ⟨hF, hregF, ?_⟩
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+k))) = m+k) :=
    ⟨finrank_euclideanSpace_fin⟩
  let : ∀ j, ChartedSpace (EuclideanSpace ℝ (Fin m))
      (openFiber (f j) (U j) (v j)) :=
    fun j => openFiberChartedSpace (m := m) (hf j) (U j) (hreg j) (v j)
  let : ∀ j, IsManifold (𝓡 m) ∞ (openFiber (f j) (U j) (v j)) :=
    fun j => isManifold_openFiber (m := m) (hf j) (U j) (hreg j) (v j)
  let : ∀ j, ChartedSpace (EuclideanSpace ℝ (Fin m))
      (openFiber (F j) (U j) (w j)) :=
    fun j => openFiberChartedSpace (m := m) (hF j) (U j) (hregF j) (w j)
  let : ∀ j, IsManifold (𝓡 m) ∞ (openFiber (F j) (U j) (w j)) :=
    fun j => isManifold_openFiber (m := m) (hF j) (U j) (hregF j) (w j)
  let gOld := fun j => PoincareConjecture.RiemannianMetric.openRegularFiberMetric
    (hf j) (U j) (hreg j) (v j) (g j)
  let gNew := fun j => PoincareConjecture.RiemannianMetric.openRegularFiberMetric
    (hF j) (U j) (hregF j) (w j) (G j)
  choose e hinc hmetric hdist hcomplete using hdata
  let Knew := fun j y => r j ^ (2 : ℕ) * K j ((e j).toEquiv.symm y)
  refine ⟨e, Knew, hinc, hmetric, fun _ _ => rfl, ?_⟩
  apply Filter.tendsto_atTop_mono' Filter.atTop ?_ hdiv
  filter_upwards [hr1] with j hj
  have ha : 1 ≤ a j :=
    (one_le_inv₀ (sq_pos_of_pos (hr j))).mpr (by nlinarith only [hr j, hj])
  have hs : Real.sqrt (a j) * r j = 1 := by
    dsimp [a]
    rw [Real.sqrt_inv, Real.sqrt_sq (hr j).le]
    exact inv_mul_cancel₀ (hr j).ne'
  have hs' : Real.sqrt (a j) * (b * r j) = b := by
    calc
      _ = b * (Real.sqrt (a j) * r j) := by ring
      _ = b := by rw [hs, mul_one]
  have himage (s : ℝ) :
      (e j) '' {x | openFiberIncl (f j) (U j) (v j) x ∈ (g j).ball (p j) s} =
        {y | openFiberIncl (F j) (U j) (w j) y ∈ (G j).ball (p j)
          (Real.sqrt (a j) * s)} :=
    (g j).image_preimage_ball_rescaledMetric
      (inv_pos.mpr (sq_pos_of_pos (hr j))) (e j).toEquiv
      (openFiberIncl (f j) (U j) (v j)) (openFiberIncl (F j) (U j) (w j))
      (hinc j) (p j) s
  have hb := (gOld j).leviCivitaData.normalized_pos_scalar_integral_le_of_metric_similarity
    (gNew j).leviCivitaData hm (e j) ha (hmetric j) (K j) (hK j)
    {x | openFiberIncl (f j) (U j) (v j) x ∈ (g j).ball (p j) (r j)}
    {x | openFiberIncl (f j) (U j) (v j) x ∈ (g j).ball (p j) (b * r j)}
  rw [himage (r j), himage (b * r j), hs, hs'] at hb
  simp only [a, inv_inv] at hb
  exact hb
