import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Annular.AncientLimit
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Coefficients.Distance













noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace Poincare.AncientVolume.ScalarRatio

private theorem exists_uniform_lipschitz_limit_on_closedBall
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (r : ℝ) (u : ℕ → E → ℝ) (C : ℝ≥0)
    (hLip : ∀ k, LipschitzOnWith C (u k) (closedBall 0 r))
    (B : ℝ) (hbound : ∀ k x, x ∈ closedBall 0 r → |u k x| ≤ B) :
    ∃ τ : ℕ → ℕ, StrictMono τ ∧ ∃ f : E → ℝ,
      LipschitzOnWith C f (closedBall 0 r) ∧
      TendstoUniformlyOn (fun k => u (τ k)) f atTop (closedBall 0 r) := by
  classical
  let X := closedBall (0 : E) r
  let : CompactSpace X := isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : E) r)
  let v : ℕ → C(X, ℝ) := fun k =>
    ⟨fun x => u k x, continuousOn_iff_continuous_domRestrict.mp (hLip k).continuousOn⟩
  have hLi (k : ℕ) : LipschitzWith C (fun x : X => v k x) :=
    fun x y => hLip k x.property y.property
  have hc : IsCompact (closure (range v)) := by
    apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
      (F := fun w : C(X, ℝ) => (w : X → ℝ))
      (𝔖 := {K | IsCompact K}) (fun _ h => h)
      (show Topology.IsClosedEmbedding (ContinuousMap.toUniformOnFunIsCompact :
        C(X, ℝ) → UniformOnFun X ℝ {K | IsCompact K}) from
        ⟨ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isEmbedding, by
          rw [ContinuousMap.range_toUniformOnFunIsCompact]
          exact UniformOnFun.isClosed_setOfPred_continuous CompactlyCoherentSpace.isCoherentWith⟩)
    · intro K hK
      have heq : Equicontinuous (fun w : range v => (w.val : X → ℝ)) := by
        apply (LipschitzWith.uniformEquicontinuous _ C _).equicontinuous
        rintro ⟨w, k, rfl⟩
        exact hLi k
      exact heq.equicontinuousOn K
    · intro K hK x hx
      refine ⟨closedBall (0 : ℝ) B, isCompact_closedBall _ _, ?_⟩
      rintro w ⟨k, rfl⟩
      simpa only [mem_closedBall, Real.dist_eq, sub_zero, v, ContinuousMap.coe_mk] using
        hbound k x x.property
  obtain ⟨a, _, τ, hτ, hlim⟩ := hc.tendsto_subseq
    (fun k => subset_closure (mem_range_self k))
  have hu := ContinuousMap.tendsto_iff_tendstoUniformly.mp hlim
  let f : E → ℝ := fun x => if hx : x ∈ closedBall 0 r then a ⟨x, hx⟩ else 0
  have hf (x : X) : f x = a x := by
    exact dif_pos (show (x : E) ∈ closedBall 0 r from x.property)
  have hpoint (x : E) (hx : x ∈ closedBall 0 r) :
      Tendsto (fun k => u (τ k) x) atTop (𝓝 (f x)) := by
    simpa only [Function.comp_apply, v, ContinuousMap.coe_mk, ← hf] using
      hu.tendsto_at (⟨x, hx⟩ : X)
  refine ⟨τ, hτ, f, ?_, ?_⟩
  · apply lipschitzOnWith_iff_dist_le_mul.mpr
    intro x hx y hy
    exact le_of_tendsto ((hpoint x hx).dist (hpoint y hy))
      (Eventually.of_forall (fun k => (hLip (τ k)).dist_le_mul x hx y hy))
  · rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
    have heq : f ∘ Subtype.val = (a : X → ℝ) := funext hf
    rw [heq]
    exact hu

end Poincare.AncientVolume.ScalarRatio

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [PreconnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

private theorem radial_square_lipschitz_of_normal_chart_upper
    (g : RiemannianMetric n M) (p q : M)
    (Φ : PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞)
    {r R S D b : ℝ} (hr : 0 ≤ r) (hrR : r < R) (hRS : R ≤ S)
    (hD : 0 ≤ D) (hb : 0 ≤ b) (hsource : Φ.source = Metric.ball 0 S)
    (hcenter : (g.edist p q).toReal ≤ D)
    (hradial : ∀ x ∈ Metric.ball 0 S, g.edist q (Φ x) = ENNReal.ofReal ‖x‖)
    (hupper : ∀ x ∈ Metric.ball 0 R, ∀ v : EuclideanSpace ℝ (Fin n),
      g.pullbackCoefficients Φ x v v ≤ b * ‖v‖ ^ 2) :
    LipschitzOnWith ⟨(D + r) * Real.sqrt b, by positivity⟩
      (fun x => (g.edist p (Φ x)).toReal ^ 2 / 2) (closedBall 0 r) ∧
      ∀ x ∈ closedBall 0 r, |(g.edist p (Φ x)).toReal ^ 2 / 2| ≤ (D + r) ^ 2 / 2 := by
  let := g.toMetricSpace
  have hsub : closedBall (0 : EuclideanSpace ℝ (Fin n)) r ⊆ Metric.ball 0 R :=
    closedBall_subset_ball hrR
  have hs : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R ⊆ Metric.ball 0 S :=
    Metric.ball_subset_ball hRS
  have hdist {x y : EuclideanSpace ℝ (Fin n)}
      (hx : x ∈ closedBall 0 r) (hy : y ∈ closedBall 0 r) :
      dist (Φ x) (Φ y) ≤ Real.sqrt b * dist x y :=
    g.toReal_edist_le_of_pullback_upper isOpen_ball (convex_ball _ _)
      (Φ.contMDiffOn.mono (by rw [hsource]; exact hs)) hb hupper (hsub hx) (hsub hy)
  have hrad (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ closedBall 0 r) :
      dist p (Φ x) ≤ D + r := by
    have hqx : dist q (Φ x) = ‖x‖ := by
      change (g.edist q (Φ x)).toReal = ‖x‖
      rw [hradial x (hs (hsub hx)), ENNReal.toReal_ofReal (norm_nonneg x)]
    have hnorm : ‖x‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hx
    exact (dist_triangle p q (Φ x)).trans (by
      change dist p q ≤ D at hcenter
      rw [hqx]
      linarith)
  constructor
  · apply lipschitzOnWith_iff_dist_le_mul.mpr
    intro x hx y hy
    change |dist p (Φ x) ^ 2 / 2 - dist p (Φ y) ^ 2 / 2| ≤ _
    have hdiff : |dist p (Φ x) - dist p (Φ y)| ≤ Real.sqrt b * dist x y := by
      have hh : |dist p (Φ x) - dist p (Φ y)| ≤ dist (Φ x) (Φ y) := by
        simpa only [dist_comm] using abs_dist_sub_le (Φ x) (Φ y) p
      exact hh.trans (hdist hx hy)
    have hsum : dist p (Φ x) + dist p (Φ y) ≤ 2 * (D + r) := by
      linarith [hrad x hx, hrad y hy]
    calc
      |dist p (Φ x) ^ 2 / 2 - dist p (Φ y) ^ 2 / 2| =
          |dist p (Φ x) - dist p (Φ y)| * (dist p (Φ x) + dist p (Φ y)) / 2 := by
        rw [show dist p (Φ x) ^ 2 / 2 - dist p (Φ y) ^ 2 / 2 =
          (dist p (Φ x) - dist p (Φ y)) * (dist p (Φ x) + dist p (Φ y)) / 2 by ring,
          abs_div, abs_mul, abs_of_nonneg (add_nonneg dist_nonneg dist_nonneg)]
        norm_num
      _ ≤ (Real.sqrt b * dist x y) * (2 * (D + r)) / 2 :=
        div_le_div_of_nonneg_right
          (mul_le_mul hdiff hsum (add_nonneg dist_nonneg dist_nonneg) (by positivity)) (by norm_num)
      _ = ((⟨(D + r) * Real.sqrt b, by positivity⟩ : ℝ≥0) : ℝ) * dist x y := by
        ring
  · intro x hx
    change |dist p (Φ x) ^ 2 / 2| ≤ _
    rw [abs_of_nonneg (by positivity)]
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ dist_nonneg (hrad x hx) 2) (by norm_num)




theorem exists_radial_square_limit_of_normal_chart_coefficients
    (g : ℕ → RiemannianMetric n M) (p : M) (q : ℕ → M)
    (Φ : ℕ → PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞)
    {R S d : ℝ} (hR : 0 < R) (hRS : R ≤ S)
    (hsource : ∀ k, (Φ k).source = Metric.ball 0 S)
    (hzero : ∀ k, Φ k 0 = q k)
    (hradial : ∀ k x, x ∈ Metric.ball 0 S →
      (g k).edist (q k) (Φ k x) = ENNReal.ofReal ‖x‖)
    (hcenter : Tendsto (fun k => ((g k).edist p (q k)).toReal) atTop (𝓝 d))
    (B : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hB : ContinuousOn B (closedBall 0 R))
    (hcoeff : TendstoUniformlyOn (fun k => (g k).pullbackCoefficients (Φ k))
      B atTop (closedBall 0 R)) :
    ∃ τ : ℕ → ℕ, StrictMono τ ∧ ∃ C : ℝ≥0, ∃ f : EuclideanSpace ℝ (Fin n) → ℝ,
      LipschitzOnWith C f (closedBall 0 (R / 2)) ∧
      TendstoUniformlyOn
        (fun k x => ((g (τ k)).edist p (Φ (τ k) x)).toReal ^ 2 / 2)
        f atTop (closedBall 0 (R / 2)) ∧
      f 0 = d ^ 2 / 2 ∧ (∀ x ∈ closedBall 0 (R / 2), 0 ≤ f x) ∧
      TendstoUniformlyOn (fun k => (g (τ k)).pullbackCoefficients (Φ (τ k)))
        B atTop (closedBall 0 R) := by
  obtain ⟨b₀, hb₀⟩ :=
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) R).exists_bound_of_continuousOn
      (f := B) hB
  let b := max b₀ 0 + 1
  have hb : 0 ≤ b := by dsimp [b]; positivity
  let D := |d| + 1
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hcoeffBound : ∀ᶠ k in atTop, ∀ x ∈ closedBall 0 R,
      ‖(g k).pullbackCoefficients (Φ k) x‖ ≤ b := by
    filter_upwards [(Metric.tendstoUniformlyOn_iff (f := B)).mp hcoeff 1 zero_lt_one]
      with k hk x hx
    have hdist : ‖(g k).pullbackCoefficients (Φ k) x - B x‖ < 1 := by
      calc
        ‖(g k).pullbackCoefficients (Φ k) x - B x‖ =
            ‖B x - (g k).pullbackCoefficients (Φ k) x‖ :=
          norm_sub_rev ((g k).pullbackCoefficients (Φ k) x) (B x)
        _ = dist (B x) ((g k).pullbackCoefficients (Φ k) x) :=
          (dist_eq_norm (B x) ((g k).pullbackCoefficients (Φ k) x)).symm
        _ < 1 := hk x hx
    calc
      ‖(g k).pullbackCoefficients (Φ k) x‖ ≤
          ‖(g k).pullbackCoefficients (Φ k) x - B x‖ + ‖B x‖ := by
        exact norm_le_norm_sub_add ((g k).pullbackCoefficients (Φ k) x) (B x)
      _ ≤ b := by have := hb₀ x hx; dsimp [b]; linarith [le_max_left b₀ 0]
  have hcenterBound : ∀ᶠ k in atTop, ((g k).edist p (q k)).toReal ≤ D := by
    filter_upwards [hcenter.eventually_lt_const (show d < |d| + 1 by linarith [le_abs_self d])]
      with k hk
    exact hk.le
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hcoeffBound.and hcenterBound)
  let C : ℝ≥0 := ⟨(D + R / 2) * Real.sqrt b, by positivity⟩
  let u : ℕ → EuclideanSpace ℝ (Fin n) → ℝ :=
    fun k x => ((g (k + N)).edist p (Φ (k + N) x)).toReal ^ 2 / 2
  have hgood (k : ℕ) :
      LipschitzOnWith C (u k) (closedBall 0 (R / 2)) ∧
      ∀ x ∈ closedBall 0 (R / 2), |u k x| ≤ (D + R / 2) ^ 2 / 2 := by
    apply radial_square_lipschitz_of_normal_chart_upper (g (k + N)) p (q (k + N))
      (Φ (k + N)) (by positivity) (by linarith) hRS hD hb
      (hsource (k + N)) (hN (k + N) (by omega)).2 (hradial (k + N))
    intro x hx v
    let T := (g (k + N)).pullbackCoefficients (Φ (k + N)) x
    have hT : ‖T‖ ≤ b := (hN (k + N) (by omega)).1 x (ball_subset_closedBall hx)
    calc
      T v v ≤ ‖T v v‖ := le_abs_self _
      _ ≤ ‖T v‖ * ‖v‖ := (T v).le_opNorm v
      _ ≤ (‖T‖ * ‖v‖) * ‖v‖ := mul_le_mul_of_nonneg_right (T.le_opNorm v) (norm_nonneg v)
      _ ≤ b * ‖v‖ ^ 2 := by nlinarith [sq_nonneg ‖v‖]
  obtain ⟨τ, hτ, f, hLip, hlim⟩ :=
    Poincare.AncientVolume.ScalarRatio.exists_uniform_lipschitz_limit_on_closedBall
      (R / 2) u C (fun k => (hgood k).1) ((D + R / 2) ^ 2 / 2)
      (fun k => (hgood k).2)
  let σ : ℕ → ℕ := fun k => τ k + N
  have hσ : StrictMono σ := fun i j hij => Nat.add_lt_add_right (hτ hij) N
  have hlim' : TendstoUniformlyOn
      (fun k x => ((g (σ k)).edist p (Φ (σ k) x)).toReal ^ 2 / 2)
      f atTop (closedBall 0 (R / 2)) := hlim
  refine ⟨σ, hσ, C, f, hLip, hlim', ?_, ?_, ?_⟩
  · have hsource0 : Tendsto
        (fun k => ((g (σ k)).edist p (Φ (σ k) 0)).toReal ^ 2 / 2)
        atTop (𝓝 (d ^ 2 / 2)) := by
      simpa only [hzero, Function.comp_apply] using
        ((hcenter.comp hσ.tendsto_atTop).pow 2).div_const 2
    exact tendsto_nhds_unique (hlim'.tendsto_at (mem_closedBall_self (by positivity))) hsource0
  · intro x hx
    exact ge_of_tendsto (hlim'.tendsto_at hx) (Eventually.of_forall (fun k => by positivity))
  · intro V hV
    exact hσ.tendsto_atTop.eventually (hcoeff V hV)

end PoincareConjecture.RiemannianMetric

namespace PoincareConjecture.RicciFlow





theorem exists_radial_square_potential_of_normalized_annular_limit
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [PreconnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (F : RicciFlow n M (Iic 0)) (t₀ : ℝ) (ht₀ : t₀ ≤ 0) (p : M) (q : ℕ → M)
    (hQ : ∀ i, 0 < (F.connection t₀).scalarCurvature (q i))
    {A : ℝ} (hA : 0 < A)
    (hratio : Tendsto (fun i => (F.connection t₀).scalarCurvature (q i) *
      ((F.metric t₀).edist p (q i)).toReal ^ 2) atTop (𝓝 A))
    (σ : ℕ → ℕ) (hσ : StrictMono σ) {ρ S : ℝ} (hρ : 0 < ρ) (hρS : ρ ≤ S)
    (Φ : ℕ → PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞)
    (hsource : ∀ k, (Φ k).source = ball 0 S) (hzero : ∀ k, Φ k 0 = q (σ k))
    (B : ℝ × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hB : ContDiffOn ℝ ∞ B (Iic 0 ×ˢ closedBall 0 ρ)) :
    let G := fun k => F.ancientRescaleAt
      ((F.connection t₀).scalarCurvature (q (σ k))) (hQ (σ k)) t₀ ht₀
    (∀ k x, x ∈ ball 0 S → ((G k).metric 0).edist (q (σ k)) (Φ k x) =
      ENNReal.ofReal ‖x‖) →
    (∀ m E, IsCompact E → E ⊆ Iic 0 ×ˢ closedBall 0 ρ → TendstoUniformlyOn
      (fun k => iteratedFDerivWithin ℝ m
        (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
          ((G k).metric z.1).pullbackCoefficients (Φ k) z.2)
        (Iic 0 ×ˢ closedBall 0 ρ))
      (iteratedFDerivWithin ℝ m B (Iic 0 ×ˢ closedBall 0 ρ)) atTop E) →
    ∃ τ : ℕ → ℕ, StrictMono τ ∧ ∃ C : ℝ≥0, ∃ f : EuclideanSpace ℝ (Fin n) → ℝ,
      LipschitzOnWith C f (closedBall 0 (ρ / 2)) ∧
      TendstoUniformlyOn
        (fun k x => (((G (τ k)).metric 0).edist p (Φ (τ k) x)).toReal ^ 2 / 2)
        f atTop (closedBall 0 (ρ / 2)) ∧
      f 0 = A / 2 ∧ 0 < f 0 ∧ (∀ x ∈ closedBall 0 (ρ / 2), 0 ≤ f x) ∧
      (∀ m E, IsCompact E → E ⊆ Iic 0 ×ˢ closedBall 0 ρ → TendstoUniformlyOn
        (fun k => iteratedFDerivWithin ℝ m
          (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
            ((G (τ k)).metric z.1).pullbackCoefficients (Φ (τ k)) z.2)
          (Iic 0 ×ˢ closedBall 0 ρ))
        (iteratedFDerivWithin ℝ m B (Iic 0 ×ˢ closedBall 0 ρ)) atTop E) := by
  dsimp only
  let G := fun k => F.ancientRescaleAt
    ((F.connection t₀).scalarCurvature (q (σ k))) (hQ (σ k)) t₀ ht₀
  intro hradial hjets
  have hcenter : Tendsto (fun k => (((G k).metric 0).edist p (q (σ k))).toReal)
      atTop (𝓝 (Real.sqrt A)) :=
    (F.ancientRescaleAt_basepoint_edist_tendsto_of_finite_ratio t₀ ht₀ p q hQ hratio).comp
      hσ.tendsto_atTop
  have hslice : ContinuousOn (fun x => B (0, x)) (closedBall 0 ρ) :=
    (hB.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun x hx => ⟨by simp, hx⟩)).continuousOn
  have hcoeff : TendstoUniformlyOn (fun k => ((G k).metric 0).pullbackCoefficients (Φ k))
      (fun x => B (0, x)) atTop (closedBall 0 ρ) := by
    have hzerojet := hjets 0 ({0} ×ˢ closedBall 0 ρ)
      (isCompact_singleton.prod (isCompact_closedBall _ _))
      (fun z hz => ⟨le_of_eq (mem_singleton_iff.mp hz.1), hz.2⟩)
    have hvalue := (ContinuousMultilinearMap.uniformContinuous_eval_const
      (0 : Fin 0 → ℝ × EuclideanSpace ℝ (Fin n))).comp_tendstoUniformlyOn hzerojet
    have hcomp := (hvalue.comp (fun x : EuclideanSpace ℝ (Fin n) => (0, x))).mono
      (show closedBall (0 : EuclideanSpace ℝ (Fin n)) ρ ⊆
        (fun x => (0, x)) ⁻¹' ({0} ×ˢ closedBall 0 ρ) from fun _ hx => ⟨rfl, hx⟩)
    simpa only [Function.comp_def, iteratedFDerivWithin_zero_apply] using hcomp
  obtain ⟨τ, hτ, C, f, hLip, hlim, hf0, hfnonneg, _⟩ :=
    RiemannianMetric.exists_radial_square_limit_of_normal_chart_coefficients
      (fun k => (G k).metric 0) p (fun k => q (σ k)) Φ hρ hρS hsource hzero hradial
      hcenter (fun x => B (0, x)) hslice hcoeff
  have hvalue : f 0 = A / 2 := by simpa only [Real.sq_sqrt hA.le] using hf0
  refine ⟨τ, hτ, C, f, hLip, hlim, hvalue, by rw [hvalue]; positivity, hfnonneg, ?_⟩
  intro m E hE hsub V hV
  exact hτ.tendsto_atTop.eventually (hjets m E hE hsub V hV)

end PoincareConjecture.RicciFlow
