import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.SUAlphaCoordinateCompactness
import PoincareConjecture.Proofs.M40.Mathlib.SupportedChartSmoothing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Uniformity
open scoped Manifold ContDiff Topology Bundle BoundedContinuousFunction ENNReal

noncomputable section

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

namespace M60

theorem suAlpha_supported_competitor
    (g : RiemannianMetric n M) (alpha : ℝ) (p : UnitTwoSphere) (b : M)
    (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f)
    (hn : ¬ IsNullHomotopicSphere f)
    (rho : UnitTwoSphere → ℝ) (hrho : ContMDiff (𝓡 2) 𝓘(ℝ) ∞ rho)
    (hrange : ∀ x, rho x ∈ Icc 0 1)
    (G : LoopPlane → EuclideanSpace ℝ (Fin n)) (hG : ContDiff ℝ ∞ G)
    {U : Set UnitTwoSphere} (hU : IsOpen U)
    (hUs : U ⊆ (chartAt LoopPlane p).source) (hsupp : tsupport rho ⊆ U)
    (hfU : MapsTo f U (chartAt (EuclideanSpace ℝ (Fin n)) b).source)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : Convex ℝ K)
    (hKt : K ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) b).target)
    (hfK : MapsTo ((chartAt (EuclideanSpace ℝ (Fin n)) b) ∘ f) U K)
    (hGK : MapsTo (G ∘ (chartAt LoopPlane p)) U K) :
    ∃ F : UnitTwoSphere → M, ContMDiff (𝓡 2) (𝓡 n) ∞ F ∧
      ¬ IsNullHomotopicSphere F ∧
      sInf (m60NonNullAlphaEnergyValues g alpha) ≤ m60SphereAlphaEnergy g alpha F ∧
      (∀ x ∈ U, F x ∈ (chartAt (EuclideanSpace ℝ (Fin n)) b).source ∧
        (chartAt (EuclideanSpace ℝ (Fin n)) b) (F x) =
          (1 - rho x) • (chartAt (EuclideanSpace ℝ (Fin n)) b) (f x) +
            rho x • G ((chartAt LoopPlane p) x)) ∧
      ∀ x ∉ tsupport rho, F =ᶠ[𝓝 x] f := by
  let s := chartAt LoopPlane p
  let c := chartAt (EuclideanSpace ℝ (Fin n)) b
  have hvalid (t : unitInterval) (x : UnitTwoSphere) (hx : x ∈ U) :
      c (f x) + (t : ℝ) • M40.chartSmoothingDisplacement s c rho f G x ∈ c.target := by
    have ha : 0 ≤ (t : ℝ) * rho x := mul_nonneg t.property.1 (hrange x).1
    have hb : (t : ℝ) * rho x ≤ 1 := by
      calc
        _ ≤ 1 * rho x := mul_le_mul_of_nonneg_right t.property.2 (hrange x).1
        _ ≤ 1 := by simpa only [one_mul] using (hrange x).2
    have hid : c (f x) + (t : ℝ) • M40.chartSmoothingDisplacement s c rho f G x =
        (1 - (t : ℝ) * rho x) • c (f x) + ((t : ℝ) * rho x) • G (s x) := by
      dsimp only [M40.chartSmoothingDisplacement]
      module
    rw [hid]
    exact hKt (hK (hfK hx) (hGK hx) (sub_nonneg.mpr hb) ha (by ring))
  let F := M40.supportedChartSmoothing s c U rho f G
  have hF : ContMDiff (𝓡 2) (𝓡 n) ∞ F := fun x =>
    M40.contMDiffAt_supportedChartSmoothing_of_contMDiffAt s c hU hUs hrho hG
      contMDiffOn_chart contMDiffOn_chart contMDiffOn_chart_symm hsupp hfU
      (fun x hx => by simpa using hvalid 1 x hx) (hf x)
  have hhom : (⟨f, hf.continuous⟩ : C(UnitTwoSphere, M)).Homotopic
      ⟨F, hF.continuous⟩ :=
    ⟨M40.supportedChartSmoothingHomotopy s c hU hUs rho ⟨f, hf.continuous⟩ G
      hrho.continuous hG.continuous hsupp hfU hvalid⟩
  have hnF : ¬ IsNullHomotopicSphere F := by
    rintro ⟨_, x, hx⟩
    exact hn ⟨hf.continuous, x, hhom.trans hx⟩
  refine ⟨F, hF, hnF, csInf_le (m60NonNullAlphaEnergyValues_bddBelow g alpha)
    ⟨F, hF, hnF, rfl⟩, ?_, ?_⟩
  · intro x hx
    have hmem : (1 - rho x) • c (f x) + rho x • G (s x) ∈ c.target :=
      hKt (hK (hfK hx) (hGK hx) (sub_nonneg.mpr (hrange x).2) (hrange x).1 (by ring))
    have heq : F x = c.symm ((1 - rho x) • c (f x) + rho x • G (s x)) := by
      rw [show F x = c.symm (M40.cutoffBlend rho (c ∘ f) (G ∘ s) x) from
        M40.supportedChartSmoothing_of_mem s c U rho f G hx]
      congr 1
      dsimp only [M40.cutoffBlend, Function.comp_apply]
      module
    exact ⟨heq ▸ c.map_target hmem, by rw [heq, c.right_inv hmem]⟩
  · exact fun x hx => M40.supportedChartSmoothing_eventuallyEq s c U rho f G hfU hx

theorem suAlpha_supported_energy_difference
    (g : RiemannianMetric n M) {alpha : ℝ} (ha : 0 ≤ alpha) (p : UnitTwoSphere)
    (f F : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f)
    (hF : ContMDiff (𝓡 2) (𝓡 n) ∞ F) {S : Set LoopPlane} (hS : MeasurableSet S)
    (hfix : ∀ z ∉ S, F ∘ (chartAt LoopPlane p).symm =ᶠ[𝓝 z]
      f ∘ (chartAt LoopPlane p).symm) :
    m60SphereAlphaEnergy g alpha F - m60SphereAlphaEnergy g alpha f =
      ∫ z in S, suSphereChartAlphaDensity g alpha p F z -
        suSphereChartAlphaDensity g alpha p f z := by
  obtain ⟨hfi, hfeq⟩ := suSphereChartAlphaDensity_integral g ha p f hf
  obtain ⟨hFi, hFeq⟩ := suSphereChartAlphaDensity_integral g ha p F hF
  rw [hfeq, hFeq, ← integral_sub hFi hfi, ← integral_indicator hS]
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : z ∈ S
  · simp only [indicator_of_mem hz]
  · rw [indicator_of_notMem hz]
    apply sub_eq_zero.mpr
    dsimp only [suSphereChartAlphaDensity]
    rw [m60EnergyDensity_congr_of_eventuallyEq g (hfix z hz)]

set_option maxHeartbeats 1600000 in

set_option synthInstance.maxHeartbeats 100000 in

theorem suAlpha_local_pair_integral
    (g : RiemannianMetric n M) {alpha R a C D L d s delta : ℝ}
    (ha : 1 ≤ alpha) (ha0 : 0 < a) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hd : 0 ≤ d) (hs : 0 < s) (p : UnitTwoSphere) (b : M)
    (rho : UnitTwoSphere → ℝ) (hrho : ContMDiff (𝓡 2) 𝓘(ℝ) ∞ rho)
    (hrange : ∀ x, rho x ∈ Icc 0 (1 / 2))
    (hsupp : tsupport rho ⊆ (chartAt LoopPlane p).source ∩
      (chartAt LoopPlane p) ⁻¹' Metric.ball ((chartAt LoopPlane p) p) R)
    (e : M → EuclideanSpace ℝ (Fin n)) (he : ContMDiff (𝓡 n) (𝓡 n) ∞ e)
    (f₁ f₂ : UnitTwoSphere → M)
    (hf₁ : ContMDiff (𝓡 2) (𝓡 n) ∞ f₁) (hf₂ : ContMDiff (𝓡 2) (𝓡 n) ∞ f₂)
    (hn₁ : ¬ IsNullHomotopicSphere f₁) (hn₂ : ¬ IsNullHomotopicSphere f₂)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : Convex ℝ K)
    (hKt : K ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) b).target)
    (hcoord₁ : ∀ x ∈ (chartAt LoopPlane p).source ∩
      (chartAt LoopPlane p) ⁻¹' Metric.ball ((chartAt LoopPlane p) p) R,
      f₁ x ∈ (chartAt (EuclideanSpace ℝ (Fin n)) b).source ∧
        e (f₁ x) = (chartAt (EuclideanSpace ℝ (Fin n)) b) (f₁ x) ∧ e (f₁ x) ∈ K)
    (hcoord₂ : ∀ x ∈ (chartAt LoopPlane p).source ∩
      (chartAt LoopPlane p) ⁻¹' Metric.ball ((chartAt LoopPlane p) p) R,
      f₂ x ∈ (chartAt (EuclideanSpace ℝ (Fin n)) b).source ∧
        e (f₂ x) = (chartAt (EuclideanSpace ℝ (Fin n)) b) (f₂ x) ∧ e (f₂ x) ∈ K)
    (hmetric : ∀ y ∈ K, ∀ v, a * ‖v‖ ^ 2 ≤
      g.pullbackCoefficients (chartAt (EuclideanSpace ℝ (Fin n)) b).symm y v v)
    (hnorm : ∀ y ∈ K,
      ‖g.pullbackCoefficients (chartAt (EuclideanSpace ℝ (Fin n)) b).symm y‖ ≤ C)
    (hosc : ∀ y ∈ K, ∀ w ∈ K, ‖y - w‖ ≤ delta →
      ‖g.pullbackCoefficients (chartAt (EuclideanSpace ℝ (Fin n)) b).symm y -
        g.pullbackCoefficients (chartAt (EuclideanSpace ℝ (Fin n)) b).symm w‖ ≤ d / 2)
    (hclose : ∀ z ∈ Metric.ball ((chartAt LoopPlane p) p) R,
      ‖e (f₁ ((chartAt LoopPlane p).symm z)) - e (f₂ ((chartAt LoopPlane p).symm z))‖ ≤
        min s delta)
    (hcut : ∀ z ∈ Metric.ball ((chartAt LoopPlane p) p) R,
      ‖fderiv ℝ (rho ∘ (chartAt LoopPlane p).symm) z‖ ≤ D)
    (hweight : ∀ z ∈ Metric.ball ((chartAt LoopPlane p) p) R,
      (16 / (‖z‖ ^ 2 + 4) ^ 2) ^ (1 - alpha) ≤ L) :
    let T := (1 + d / a) ^ alpha
    let S := (1 + s) ^ (2 * alpha)
    (a / 4) ^ alpha * (∫ z in Metric.ball ((chartAt LoopPlane p) p) R,
      rho ((chartAt LoopPlane p).symm z) *
        ‖suAlphaDerivativePair (e ∘ f₁ ∘ (chartAt LoopPlane p).symm) z -
          suAlphaDerivativePair (e ∘ f₂ ∘ (chartAt LoopPlane p).symm) z‖ ^ (2 * alpha)) ≤
      T ^ 2 * S * (m60SphereAlphaEnergy g alpha f₁ + m60SphereAlphaEnergy g alpha f₂) -
        2 * sInf (m60NonNullAlphaEnergyValues g alpha) +
        2 * T * S * s * (1 + 2 * C * D ^ 2) ^ alpha * L *
          (volume (Metric.ball ((chartAt LoopPlane p) p) R)).toReal := by
  let c := chartAt (EuclideanSpace ℝ (Fin n)) b
  let cs := chartAt LoopPlane p
  let O := Metric.ball (cs p) R
  let U := cs.source ∩ cs ⁻¹' O
  let u₁ := e ∘ f₁ ∘ cs.symm
  let u₂ := e ∘ f₂ ∘ cs.symm
  let eta := rho ∘ cs.symm
  let v₁ := fun z => (1 - eta z) • u₁ z + eta z • u₂ z
  let v₂ := fun z => (1 - eta z) • u₂ z + eta z • u₁ z
  let B := fun y => suAlphaPairMetric (g.pullbackCoefficients c.symm y)
  let T := (1 + d / a) ^ alpha
  let S := (1 + s) ^ (2 * alpha)
  let Q := T ^ 2 * S
  let err := 2 * T * S * s * (1 + 2 * C * D ^ 2) ^ alpha * L
  let gap := fun z => eta z *
    ‖suAlphaDerivativePair u₁ z - suAlphaDerivativePair u₂ z‖ ^ (2 * alpha)
  have hU : IsOpen U := cs.isOpen_inter_preimage Metric.isOpen_ball
  have hcs (z : LoopPlane) : z ∈ cs.target := suSphereChart_target p ▸ mem_univ z
  have hx (z : LoopPlane) (hz : z ∈ O) : cs.symm z ∈ U :=
    ⟨cs.map_target (hcs z), by simpa only [mem_preimage, cs.right_inv (hcs z)] using hz⟩
  have hu₁ : ContDiff ℝ ∞ u₁ := contMDiff_iff_contDiff.mp
    (he.comp (hf₁.comp (suSphereChart_smooth p)))
  have hu₂ : ContDiff ℝ ∞ u₂ := contMDiff_iff_contDiff.mp
    (he.comp (hf₂.comp (suSphereChart_smooth p)))
  have heta : ContDiff ℝ ∞ eta := contMDiff_iff_contDiff.mp (hrho.comp (suSphereChart_smooth p))
  have hrange' (x : UnitTwoSphere) : rho x ∈ Icc 0 1 :=
    ⟨(hrange x).1, by have := (hrange x).2; linarith⟩
  have hmap₁ : MapsTo (c ∘ f₁) U K := fun x hx => by
    change c (f₁ x) ∈ K
    rw [← (hcoord₁ x hx).2.1]
    exact (hcoord₁ x hx).2.2
  have hmap₂ : MapsTo (c ∘ f₂) U K := fun x hx => by
    change c (f₂ x) ∈ K
    rw [← (hcoord₂ x hx).2.1]
    exact (hcoord₂ x hx).2.2
  have ho₁ : MapsTo (u₁ ∘ cs) U K := fun x hx => by
    simpa only [u₁, Function.comp_apply, cs.left_inv hx.1] using (hcoord₁ x hx).2.2
  have ho₂ : MapsTo (u₂ ∘ cs) U K := fun x hx => by
    simpa only [u₂, Function.comp_apply, cs.left_inv hx.1] using (hcoord₂ x hx).2.2
  obtain ⟨F₁, hF₁, _, hmin₁, hval₁, hfix₁⟩ := suAlpha_supported_competitor g alpha p b
    f₁ hf₁ hn₁ rho hrho hrange' u₂ hu₂ hU (fun _ h => h.1) hsupp
      (fun x hx => (hcoord₁ x hx).1) hK hKt hmap₁ ho₂
  obtain ⟨F₂, hF₂, _, hmin₂, hval₂, hfix₂⟩ := suAlpha_supported_competitor g alpha p b
    f₂ hf₂ hn₂ rho hrho hrange' u₁ hu₁ hU (fun _ h => h.1) hsupp
      (fun x hx => (hcoord₂ x hx).1) hK hKt hmap₂ ho₁
  have hB (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ K) (v) : a * ‖v‖ ^ 2 ≤ B y v v :=
    suAlphaPairMetric_coercive _ ha0.le (hmetric y hy) v
  have hBn (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ K) : ‖B y‖ ≤ 2 * C := by
    exact (suAlphaPairMetric_norm _).trans
      (mul_le_mul_of_nonneg_left (hnorm y hy) (by norm_num))
  have hBdiff (y w : EuclideanSpace ℝ (Fin n)) (hy : y ∈ K) (hw : w ∈ K)
      (hh : ‖y - w‖ ≤ delta) : ‖B y - B w‖ ≤ d :=
    (suAlphaPairMetric_norm_sub _ _).trans (by have := hosc y hy w hw hh; linarith)
  have hT : 1 ≤ T := Real.one_le_rpow
    (by have := div_nonneg hd ha0.le; linarith) (by linarith)
  have hS : 1 ≤ S := Real.one_le_rpow (by linarith) (by linarith)
  have hQ : 1 ≤ Q := by
    have ht2 : 1 ≤ T ^ 2 := by nlinarith [sq_nonneg (T - 1)]
    have hm := mul_le_mul_of_nonneg_left hS (sq_nonneg T)
    dsimp only [Q]
    nlinarith
  have hpoint (z : LoopPlane) (hz : z ∈ O) :
      suSphereChartAlphaDensity g alpha p F₁ z + suSphereChartAlphaDensity g alpha p F₂ z +
        (a / 4) ^ alpha * gap z ≤ Q * (suSphereChartAlphaDensity g alpha p f₁ z +
          suSphereChartAlphaDensity g alpha p f₂ z) + err := by
    have hzU := hx z hz
    have h₁ := hcoord₁ _ hzU
    have h₂ := hcoord₂ _ hzU
    have hu₁K : u₁ z ∈ K := h₁.2.2
    have hu₂K : u₂ z ∈ K := h₂.2.2
    have ht : eta z ∈ Icc 0 (1 / 2) := hrange _
    have ht1 : eta z ≤ 1 := by linarith [ht.2]
    have hv₁K : v₁ z ∈ K := hK hu₁K hu₂K (sub_nonneg.mpr ht1) ht.1 (by ring)
    have hv₂K : v₂ z ∈ K := hK hu₂K hu₁K (sub_nonneg.mpr ht1) ht.1 (by ring)
    have hdist : ‖u₂ z - u₁ z‖ ≤ min s delta := by rw [norm_sub_rev]; exact hclose z hz
    have hd₁ : ‖v₁ z - u₁ z‖ ≤ delta := by
      have heq : v₁ z - u₁ z = eta z • (u₂ z - u₁ z) := by dsimp only [v₁]; module
      rw [heq, norm_smul, Real.norm_of_nonneg ht.1]
      exact (mul_le_mul_of_nonneg_right ht1 (norm_nonneg _)).trans
        (by simpa only [one_mul] using hdist.trans (min_le_right _ _))
    have hd₂ : ‖v₂ z - u₁ z‖ ≤ delta := by
      have heq : v₂ z - u₁ z = (1 - eta z) • (u₂ z - u₁ z) := by dsimp only [v₂]; module
      rw [heq, norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr ht1)]
      exact (mul_le_mul_of_nonneg_right (by linarith [ht.1] : 1 - eta z ≤ 1) (norm_nonneg _)).trans
        (by simpa only [one_mul] using hdist.trans (min_le_right _ _))
    let q := (fderiv ℝ eta z (EuclideanSpace.basisFun (Fin 2) ℝ 0) • (u₂ z - u₁ z),
      fderiv ℝ eta z (EuclideanSpace.basisFun (Fin 2) ℝ 1) • (u₂ z - u₁ z))
    have hq : ‖q‖ ≤ s * D := by
      have hcol (i : Fin 2) : ‖fderiv ℝ eta z (EuclideanSpace.basisFun (Fin 2) ℝ i)‖ ≤ D := by
        have hle : ‖fderiv ℝ eta z (EuclideanSpace.basisFun (Fin 2) ℝ i)‖ ≤ ‖fderiv ℝ eta z‖ :=
          by simpa using (fderiv ℝ eta z).le_opNorm (EuclideanSpace.basisFun (Fin 2) ℝ i)
        exact hle.trans (hcut z hz)
      apply max_le <;> rw [norm_smul]
      all_goals exact (mul_le_mul (hcol _) (hdist.trans (min_le_left _ _))
        (norm_nonneg _) hD).trans_eq (mul_comm D s)
    have hdv₁ := suAlphaDerivativePair_blend (heta.differentiable (by simp) z)
      (hu₁.differentiable (by simp) z) (hu₂.differentiable (by simp) z)
    have hdv₂ : suAlphaDerivativePair v₂ z =
        (1 - eta z) • suAlphaDerivativePair u₂ z + eta z • suAlphaDerivativePair u₁ z - q := by
      rw [suAlphaDerivativePair_blend (heta.differentiable (by simp) z)
        (hu₂.differentiable (by simp) z) (hu₁.differentiable (by simp) z)]
      dsimp only [q]
      apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub,
        Prod.smul_fst, Prod.smul_snd] <;> module
    have hden (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f)
        (v : LoopPlane → EuclideanSpace ℝ (Fin n)) (hchart : f (cs.symm z) ∈ c.source)
        (hv : c ∘ f ∘ cs.symm =ᶠ[𝓝 z] v) :
        suSphereChartAlphaDensity g alpha p f z = (16 / (‖z‖ ^ 2 + 4) ^ 2) ^ (1 - alpha) *
          suRegularizedQuadratic (B (v z)) (16 / (‖z‖ ^ 2 + 4) ^ 2) alpha
            (suAlphaDerivativePair v z) := by
      rw [suSphereChartAlphaDensity_eq_regularized g alpha p b f hf z
        (by simpa only [extChartAt_source] using hchart)]
      change _ * suRegularizedQuadratic (B ((c ∘ f ∘ cs.symm) z)) _ _ _ = _
      rw [hv.self_of_nhds]
      have hderiv : fderiv ℝ ((extChartAt (𝓡 n) b) ∘ f ∘ (chartAt LoopPlane p).symm) z =
          fderiv ℝ v z := hv.fderiv_eq
      simp only [suAlphaDerivativePair, hderiv]
    have horig₁ : c ∘ f₁ ∘ cs.symm =ᶠ[𝓝 z] u₁ := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hz] with y hy
      exact (hcoord₁ _ (hx y hy)).2.1.symm
    have horig₂ : c ∘ f₂ ∘ cs.symm =ᶠ[𝓝 z] u₂ := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hz] with y hy
      exact (hcoord₂ _ (hx y hy)).2.1.symm
    have hnew₁ : c ∘ F₁ ∘ cs.symm =ᶠ[𝓝 z] v₁ := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hz] with y hy
      have hh := (hval₁ _ (hx y hy)).2
      change c (F₁ (cs.symm y)) = (1 - rho (cs.symm y)) • c (f₁ (cs.symm y)) +
        rho (cs.symm y) • u₂ (cs (cs.symm y)) at hh
      rw [cs.right_inv (hcs y), ← (hcoord₁ _ (hx y hy)).2.1] at hh
      exact hh
    have hnew₂ : c ∘ F₂ ∘ cs.symm =ᶠ[𝓝 z] v₂ := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hz] with y hy
      have hh := (hval₂ _ (hx y hy)).2
      change c (F₂ (cs.symm y)) = (1 - rho (cs.symm y)) • c (f₂ (cs.symm y)) +
        rho (cs.symm y) • u₁ (cs (cs.symm y)) at hh
      rw [cs.right_inv (hcs y), ← (hcoord₂ _ (hx y hy)).2.1] at hh
      exact hh
    have hl : 0 < (16 : ℝ) / (‖z‖ ^ 2 + 4) ^ 2 := by positivity
    have hl1 : (16 : ℝ) / (‖z‖ ^ 2 + 4) ^ 2 ≤ 1 := by
      apply (div_le_one (by positivity)).mpr
      nlinarith [sq_nonneg ‖z‖, sq_nonneg (‖z‖ ^ 2)]
    have hw := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hl hl1 (by linarith : 1 - alpha ≤ 0)
    have h := suAlpha_paired_weighted_power_gap (B (u₁ z)) (B (u₁ z)) (B (u₂ z))
      (B (v₁ z)) (B (v₂ z)) ⟨hl.le, hl1⟩ ha ha0 hd hs ht (by positivity) hD hw (hweight z hz)
      (hB _ hu₁K) (hB _ hu₁K) (hB _ hu₂K)
      (fun v => (mul_nonneg ha0.le (sq_nonneg _)).trans (hB _ hv₁K v))
      (fun v => (mul_nonneg ha0.le (sq_nonneg _)).trans (hB _ hv₂K v))
      (hBdiff _ _ hu₁K hu₁K (by
        have hh := (norm_nonneg _).trans ((hclose z hz).trans (min_le_right _ _))
        simpa only [sub_self, norm_zero] using hh))
      (hBdiff _ _ hu₁K hu₂K ((hclose z hz).trans (min_le_right _ _)))
      (hBdiff _ _ hv₁K hu₁K hd₁) (hBdiff _ _ hv₂K hu₁K hd₂) (hBn _ hu₁K)
      (suAlphaDerivativePair u₁ z) (suAlphaDerivativePair u₂ z) q hq
    rw [hden F₁ hF₁ v₁ (hval₁ _ hzU).1 hnew₁, hden F₂ hF₂ v₂ (hval₂ _ hzU).1 hnew₂,
      hden f₁ hf₁ u₁ h₁.1 horig₁, hden f₂ hf₂ u₂ h₂.1 horig₂, hdv₁, hdv₂]
    simpa only [gap, Q, err, T, S, mul_assoc] using h
  obtain ⟨hfi₁, hfe₁⟩ :=
    suSphereChartAlphaDensity_integral g (alpha := alpha) (by linarith) p f₁ hf₁
  obtain ⟨hfi₂, hfe₂⟩ :=
    suSphereChartAlphaDensity_integral g (alpha := alpha) (by linarith) p f₂ hf₂
  obtain ⟨hFi₁, hFe₁⟩ :=
    suSphereChartAlphaDensity_integral g (alpha := alpha) (by linarith) p F₁ hF₁
  obtain ⟨hFi₂, hFe₂⟩ :=
    suSphereChartAlphaDensity_integral g (alpha := alpha) (by linarith) p F₂ hF₂
  have hdcont (u : LoopPlane → EuclideanSpace ℝ (Fin n)) (hu : ContDiff ℝ ∞ u) :
      Continuous (suAlphaDerivativePair u) :=
    ((hu.continuous_fderiv (by simp)).clm_apply continuous_const).prodMk
      ((hu.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hgap : Continuous gap := heta.continuous.mul
    ((Real.continuous_rpow_const (by linarith : 0 ≤ 2 * alpha)).comp
      ((hdcont u₁ hu₁).sub (hdcont u₂ hu₂)).norm)
  have hgi : IntegrableOn gap O :=
    (hgap.continuousOn.integrableOn_compact (isCompact_closedBall (cs p) R)).mono_set
      Metric.ball_subset_closedBall
  have hei : IntegrableOn (fun _ : LoopPlane => err) O :=
    integrableOn_const (by exact measure_ball_lt_top.ne)
  have hnonneg (f : UnitTwoSphere → M) (z : LoopPlane) :
      0 ≤ suSphereChartAlphaDensity g alpha p f z := by
    dsimp only [suSphereChartAlphaDensity]
    exact mul_nonneg (Real.rpow_nonneg (by
      have := m60EnergyDensity_nonneg g (f ∘ cs.symm) z; positivity) _) (by positivity)
  have hglobal : ∀ z, suSphereChartAlphaDensity g alpha p F₁ z +
      suSphereChartAlphaDensity g alpha p F₂ z +
      (a / 4) ^ alpha * O.indicator gap z ≤ Q * (suSphereChartAlphaDensity g alpha p f₁ z +
        suSphereChartAlphaDensity g alpha p f₂ z) + O.indicator (fun _ => err) z := by
    intro z
    by_cases hz : z ∈ O
    · simpa only [indicator_of_mem hz] using hpoint z hz
    · have hnot : cs.symm z ∉ tsupport rho := by
        intro h
        have hh := (hsupp h).2
        change cs (cs.symm z) ∈ O at hh
        apply hz
        simpa only [cs.right_inv (hcs z)] using hh
      have heq₁ := m60EnergyDensity_congr_of_eventuallyEq g
        ((hfix₁ _ hnot).comp_tendsto ((suSphereChart_smooth p).continuous.continuousAt (x := z)))
      have heq₂ := m60EnergyDensity_congr_of_eventuallyEq g
        ((hfix₂ _ hnot).comp_tendsto ((suSphereChart_smooth p).continuous.continuousAt (x := z)))
      have hd₁ : suSphereChartAlphaDensity g alpha p F₁ z =
          suSphereChartAlphaDensity g alpha p f₁ z := by
        dsimp only [suSphereChartAlphaDensity]; rw [heq₁]
      have hd₂ : suSphereChartAlphaDensity g alpha p F₂ z =
          suSphereChartAlphaDensity g alpha p f₂ z := by
        dsimp only [suSphereChartAlphaDensity]; rw [heq₂]
      simp only [indicator_of_notMem hz, mul_zero, add_zero, hd₁, hd₂]
      exact le_mul_of_one_le_left (add_nonneg (hnonneg f₁ z) (hnonneg f₂ z)) hQ
  have hgi' := hgi.integrable_indicator Metric.isOpen_ball.measurableSet
  have hei' := hei.integrable_indicator Metric.isOpen_ball.measurableSet
  have hi := integral_mono ((hFi₁.add hFi₂).add (hgi'.const_mul _))
    (((hfi₁.add hfi₂).const_mul Q).add hei') hglobal
  have hleft := integral_add (hFi₁.add hFi₂) (hgi'.const_mul ((a / 4) ^ alpha))
  have hright := integral_add ((hfi₁.add hfi₂).const_mul Q) hei'
  simp only [Pi.add_apply] at hi hleft hright
  rw [hleft, integral_add hFi₁ hFi₂, hright, integral_const_mul, integral_const_mul,
    integral_add hfi₁ hfi₂, integral_indicator Metric.isOpen_ball.measurableSet,
    integral_indicator Metric.isOpen_ball.measurableSet, setIntegral_const,
    smul_eq_mul, ← hfe₁, ← hfe₂, ← hFe₁, ← hFe₂] at hi
  change _ ≤ _
  change m60SphereAlphaEnergy g alpha F₁ + m60SphereAlphaEnergy g alpha F₂ +
    (a / 4) ^ alpha * (∫ z in O, gap z) ≤ Q * (_ + _) + _ at hi
  dsimp only [Q, err, gap, eta, u₁, u₂, O, T, S, cs] at hi
  simp only [Function.comp_apply, Measure.real] at hi
  nlinarith only [hi, hmin₁, hmin₂]

theorem suAlpha_local_affine_comparison
    (g : RiemannianMetric n M) {alpha R : ℝ} (ha : 0 ≤ alpha)
    (p : UnitTwoSphere) (b : M) (t : ℝ)
    (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f)
    (hn : ¬ IsNullHomotopicSphere f)
    (e : M → EuclideanSpace ℝ (Fin n)) (he : ContMDiff (𝓡 n) (𝓡 n) ∞ e)
    (phi : LoopPlane → EuclideanSpace ℝ (Fin n)) (hphi : ContDiff ℝ ∞ phi)
    (hcompact : HasCompactSupport phi)
    (hsub : tsupport phi ⊆ Metric.ball ((chartAt LoopPlane p) p) R)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : Convex ℝ K)
    (hKt : K ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) b).target)
    (hcoord : ∀ x ∈ (chartAt LoopPlane p).source ∩
      (chartAt LoopPlane p) ⁻¹' Metric.ball ((chartAt LoopPlane p) p) R,
      f x ∈ (chartAt (EuclideanSpace ℝ (Fin n)) b).source ∧
        e (f x) = (chartAt (EuclideanSpace ℝ (Fin n)) b) (f x) ∧ e (f x) ∈ K)
    (hvar : ∀ z ∈ Metric.ball ((chartAt LoopPlane p) p) R,
      e (f ((chartAt LoopPlane p).symm z)) + t • phi z ∈ K) :
    let cs := chartAt LoopPlane p
    let u := e ∘ f ∘ cs.symm
    let B := fun y => suAlphaPairMetric
      (g.pullbackCoefficients (extChartAt (𝓡 n) b).symm y)
    let lambda := fun z : LoopPlane => 16 / (‖z‖ ^ 2 + 4) ^ 2
    let den := fun w z => lambda z ^ (1 - alpha) *
      suRegularizedQuadratic (B (w z)) (lambda z) alpha (suAlphaDerivativePair w z)
    sInf (m60NonNullAlphaEnergyValues g alpha) - m60SphereAlphaEnergy g alpha f ≤
      ∫ z in Metric.ball (cs p) R, den (fun y => u y + t • phi y) z - den u z := by
  let cs := chartAt LoopPlane p
  let c := chartAt (EuclideanSpace ℝ (Fin n)) b
  let O := Metric.ball (cs p) R
  let U := cs.source ∩ cs ⁻¹' O
  have hU : IsOpen U := cs.isOpen_inter_preimage Metric.isOpen_ball
  have hcs (z : LoopPlane) : z ∈ cs.target := suSphereChart_target p ▸ mem_univ z
  have hx (z : LoopPlane) (hz : z ∈ O) : cs.symm z ∈ U :=
    ⟨cs.map_target (hcs z), by simpa only [mem_preimage, cs.right_inv (hcs z)] using hz⟩
  let S := cs.symm '' tsupport phi
  have hS : IsCompact S := hcompact.image (suSphereChart_smooth p).continuous
  have hSU : S ⊆ U := by
    rintro _ ⟨z, hz, rfl⟩
    exact hx z (hsub hz)
  obtain ⟨rhoMap, hzero, hone, hrange⟩ :=
    exists_contMDiffMap_zero_one_nhds_of_isClosed (𝓡 2) hU.isClosed_compl hS.isClosed
      (by exact disjoint_compl_left_iff.mpr hSU) (n := ⊤)
  let rho : UnitTwoSphere → ℝ := rhoMap
  have hrho : ContMDiff (𝓡 2) 𝓘(ℝ) ∞ rho := rhoMap.contMDiff
  have hsupp : tsupport rho ⊆ U := by
    intro x hxS
    by_contra hxU
    exact (notMem_tsupport_iff_eventuallyEq.mpr
      (hzero.filter_mono (nhds_le_nhdsSet hxU))) hxS
  have hplateau (z : LoopPlane) (hz : phi z ≠ 0) : rho (cs.symm z) = 1 :=
    hone.self_of_nhdsSet _ ⟨z, subset_tsupport phi hz, rfl⟩
  let u := e ∘ f ∘ cs.symm
  let v := fun z => u z + t • phi z
  let B := fun y => suAlphaPairMetric
    (g.pullbackCoefficients (extChartAt (𝓡 n) b).symm y)
  let lambda := fun z : LoopPlane => 16 / (‖z‖ ^ 2 + 4) ^ 2
  let den := fun w z => lambda z ^ (1 - alpha) *
    suRegularizedQuadratic (B (w z)) (lambda z) alpha (suAlphaDerivativePair w z)
  have hu : ContDiff ℝ ∞ u := contMDiff_iff_contDiff.mp
    (he.comp (hf.comp (suSphereChart_smooth p)))
  have hv : ContDiff ℝ ∞ v := hu.add (hphi.const_smul t)
  have hmap : MapsTo (c ∘ f) U K := by
    intro x hx
    change c (f x) ∈ K
    rw [← (hcoord x hx).2.1]
    exact (hcoord x hx).2.2
  have hnew : MapsTo (v ∘ cs) U K := by
    intro x hx
    have hh := hvar (cs x) hx.2
    change e (f (cs.symm (cs x))) + t • phi (cs x) ∈ K at hh
    rw [cs.left_inv hx.1] at hh
    change e (f (cs.symm (cs x))) + t • phi (cs x) ∈ K
    rw [cs.left_inv hx.1]
    exact hh
  obtain ⟨F, hF, _, hmin, hval, hfix⟩ := suAlpha_supported_competitor g alpha p b f hf hn
    rho hrho hrange v hv hU (fun _ hx => hx.1) hsupp (fun x hx => (hcoord x hx).1)
      hK hKt hmap hnew
  have hcoordF (z : LoopPlane) (hz : z ∈ O) : c (F (cs.symm z)) = v z := by
    have hh := (hval _ (hx z hz)).2
    change c (F (cs.symm z)) = (1 - rho (cs.symm z)) • c (f (cs.symm z)) +
      rho (cs.symm z) • v (cs (cs.symm z)) at hh
    rw [cs.right_inv (hcs z), ← (hcoord _ (hx z hz)).2.1] at hh
    rw [hh]
    by_cases hp : phi z = 0
    · dsimp only [v, u, Function.comp_apply]
      rw [hp]
      module
    · rw [hplateau z hp]
      simp only [sub_self, zero_smul, one_smul, zero_add]
  have hden (F' : UnitTwoSphere → M) (hF' : ContMDiff (𝓡 2) (𝓡 n) ∞ F')
      (w : LoopPlane → EuclideanSpace ℝ (Fin n)) (z : LoopPlane)
      (hz : F' (cs.symm z) ∈ c.source) (hw : c ∘ F' ∘ cs.symm =ᶠ[𝓝 z] w) :
      suSphereChartAlphaDensity g alpha p F' z = den w z := by
    rw [suSphereChartAlphaDensity_eq_regularized g alpha p b F' hF' z
      (by simpa only [extChartAt_source] using hz)]
    change _ * suRegularizedQuadratic (B ((c ∘ F' ∘ cs.symm) z)) _ _ _ = _
    rw [hw.self_of_nhds]
    have hd : fderiv ℝ ((extChartAt (𝓡 n) b) ∘ F' ∘ (chartAt LoopPlane p).symm) z =
        fderiv ℝ w z :=
      hw.fderiv_eq
    simp only [den, lambda, suAlphaDerivativePair, hd]
  have hfix' (z : LoopPlane) (hz : z ∉ O) : F ∘ cs.symm =ᶠ[𝓝 z] f ∘ cs.symm := by
    apply (hfix (cs.symm z) ?_).comp_tendsto (suSphereChart_smooth p).continuous.continuousAt
    intro hmem
    have hh := (hsupp hmem).2
    apply hz
    change cs (cs.symm z) ∈ O at hh
    simpa only [cs.right_inv (hcs z)] using hh
  have hdiff := suAlpha_supported_energy_difference g ha p f F hf hF
    Metric.isOpen_ball.measurableSet hfix'
  have heq : (∫ z in O, suSphereChartAlphaDensity g alpha p F z -
      suSphereChartAlphaDensity g alpha p f z) = ∫ z in O, den v z - den u z := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with z hz
    rw [hden F hF v z (hval _ (hx z hz)).1 (by
      filter_upwards [Metric.isOpen_ball.mem_nhds hz] with y hy using hcoordF y hy),
      hden f hf u z (hcoord _ (hx z hz)).1 (by
        filter_upwards [Metric.isOpen_ball.mem_nhds hz] with y hy using
          (hcoord _ (hx y hy)).2.1.symm)]
  rw [heq] at hdiff
  change _ ≤ ∫ z in O, den v z - den u z
  linarith

end M60

end PoincareConjecture
