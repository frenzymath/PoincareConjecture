import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AlphaCriticalJetCoefficients

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Metric
open scoped Manifold ContDiff Topology ENNReal
open Poincare.Analysis.Sobolev.Weak

noncomputable section

namespace PoincareConjecture.M60

private abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)
private abbrev Jet (n : ℕ) := E (3 * n)
private abbrev Grad (n : ℕ) := E n × E n
private abbrev Base (n : ℕ) := LoopPlane × E n
private abbrev Point (n : ℕ) := Base n × Grad n

local instance jetWeakSystemBilinearNormedGroup {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    NormedAddCommGroup (F →L[ℝ] F →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup

local instance jetWeakSystemBilinearNormedSpace {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    NormedSpace ℝ (F →L[ℝ] F →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

local instance jetWeakSystemMixedNormedGroup {n : ℕ} :
    NormedAddCommGroup (Grad n →L[ℝ] E n →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance jetWeakSystemMixedNormedSpace {n : ℕ} :
    NormedSpace ℝ (Grad n →L[ℝ] E n →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

theorem suFirstJet_coefficient_chain
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (E n) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} {b : M} {alpha : ℝ}
    {u : LoopPlane → E n} {V : Fin 2 → LoopPlane → E n} {center : LoopPlane} {R : ℝ}
    (S : SUWeakAlphaCoordinate g b alpha u V center R)
    (G : SUInitialGain u V center R) (H : SUC1HolderGain u V center G.radius)
    {r : ℝ} (hr : 0 < r) (hrH : r < H.radius / 2)
    {F : (LoopPlane × Jet n) → ℝ}
    (hF : ContDiffOn ℝ 1 F
      {z | suJetBlock (0 : Fin 3) z.2 ∈ (extChartAt (𝓡 n) b).target}) :
    MemLp (fun x => F (x, suFirstJet u x)) 2
        (volume.restrict (ball center (H.radius / 2))) ∧
      ∀ k : Fin 2,
        MemLp (fun x => fderiv ℝ F (x, suFirstJet u x)
          (EuclideanSpace.single k 1, suFirstJetWeakColumn V G.hessian k x)) 2
          (volume.restrict (ball center (H.radius / 2))) ∧
        HasWeakPartialDeriv k
          (fun x => fderiv ℝ F (x, suFirstJet u x)
            (EuclideanSpace.single k 1, suFirstJetWeakColumn V G.hessian k x))
          (fun x => F (x, suFirstJet u x)) (ball center r) := by
  let rho := H.radius / 2
  let : IsFiniteMeasure (volume.restrict (ball center (H.radius / 2))) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      (measure_ball_lt_top : volume (ball center (H.radius / 2)) < ⊤)⟩
  let U (x : LoopPlane) := (x, suFirstJet u x)
  let O : Set (LoopPlane × Jet n) :=
    {z | suJetBlock (0 : Fin 3) z.2 ∈ (extChartAt (𝓡 n) b).target}
  let K := U '' closedBall center rho
  obtain ⟨hJ, _, hW, hw⟩ := suFirstJet_weak_data G H
  have hU : ContinuousOn U (closedBall center rho) := continuousOn_id.prodMk hJ
  have hO : IsOpen O := (isOpen_extChartAt_target b).preimage
    ((suJetBlock (0 : Fin 3)).continuous.comp continuous_snd)
  have hrhoR : rho < R := (half_lt_self H.radius_pos).trans (H.radius_lt.trans G.radius_lt)
  have hmap : MapsTo U (closedBall center rho) O := by
    intro x hx
    change suJetBlock (0 : Fin 3) (suFirstJet u x) ∈ (extChartAt (𝓡 n) b).target
    rw [suJetBlock_firstJet_zero]
    exact S.coordinate_range (closedBall_subset_closedBall hrhoR.le hx)
  have hK : IsCompact K := (isCompact_closedBall center rho).image_of_continuousOn hU
  have hKO : K ⊆ O := by
    rintro _ ⟨x, hx, rfl⟩
    exact hmap hx
  have hfc : ContinuousOn (fun x => F (U x)) (closedBall center rho) :=
    hF.continuousOn.comp hU hmap
  have hdfc : ContinuousOn (fun x => fderiv ℝ F (U x)) (closedBall center rho) :=
    (hF.continuousOn_fderiv_of_isOpen hO (by norm_num)).comp hU hmap
  refine ⟨suContinuous_memLp_ball hfc, fun k => ⟨?_, ?_⟩⟩
  · exact (ContinuousLinearMap.apply ℝ ℝ (E := LoopPlane × Jet n)).memLp_of_bilin
      (p := 2) (q := ⊤) 2 (memLp_prod_iff.mpr ⟨memLp_const _, hW k⟩)
        (suContinuous_memLp_ball hdfc)
  · exact suWeakPartial_source_comp_on_compact hr hrH (suContinuous_memLp_ball hJ) hW hw
      hO hK hKO (fun x hx => mem_image_of_mem U hx) hF k

theorem suFirstJet_scalar_fderiv {n : ℕ} {P : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    {F : Point n → P →L[ℝ] ℝ} {z : LoopPlane × Jet n}
    (hF : DifferentiableAt ℝ F (suAlphaFirstJetPoint z)) (v : P)
    (w : LoopPlane × Jet n) :
    fderiv ℝ (fun y => F (suAlphaFirstJetPoint y) v) z w =
      fderiv ℝ F (suAlphaFirstJetPoint z) (suAlphaFirstJetPoint w) v := by
  have hp := (@suAlphaFirstJetPoint_contDiff n).differentiable (by simp) z
  have hd := (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp z
    (hF.hasFDerivAt.comp z hp.hasFDerivAt)
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
    suAlphaFirstJetPoint_fderiv] using congrArg (fun L => L w) hd.fderiv

theorem suWeakAlphaCoordinate_first_jet_equation
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (E n) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} {b : M} {alpha : ℝ}
    {u : LoopPlane → E n} {V : Fin 2 → LoopPlane → E n} {center : LoopPlane} {R : ℝ}
    (S : SUWeakAlphaCoordinate g b alpha u V center R) (ha : 1 ≤ alpha)
    (G : SUInitialGain u V center R) (H : SUC1HolderGain u V center G.radius)
    {r : ℝ} (hr : 0 < r) (hrH : r < H.radius / 2)
    (a : Fin (3 * n)) {phi : LoopPlane → ℝ} (hp : ContDiff ℝ ∞ phi)
    (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ ball center r) :
    (∫ x in ball center r, ∑ i : Fin 2,
      (suAlphaFirstJetCoefficients g b alpha).flux (x, suFirstJet u x)
        (suFirstJetWeakColumn V G.hessian 0 x, suFirstJetWeakColumn V G.hessian 1 x)
        (suColumnBasis a i) * fderiv ℝ phi x (EuclideanSpace.single i 1)) =
      ∫ x in ball center r, (suAlphaFirstJetCoefficients g b alpha).source
        (x, suFirstJet u x)
        (suFirstJetWeakColumn V G.hessian 0 x, suFirstJetWeakColumn V G.hessian 1 x)
        (EuclideanSpace.single a 1) * phi x := by
  classical
  let rho := H.radius / 2
  let J := suFirstJet u
  let W := suFirstJetWeakColumn V G.hessian
  let U (x : LoopPlane) := (x, J x)
  let F (a : Fin n) (i : Fin 2) (z : LoopPlane × Jet n) :=
    suAlphaJetOriginalFlux g b alpha (suAlphaFirstJetPoint z) (suColumnBasis a i)
  let B (a : Fin n) (z : LoopPlane × Jet n) :=
    suAlphaJetOriginalSource g b alpha (suAlphaFirstJetPoint z) (EuclideanSpace.single a 1)
  let DF (a : Fin n) (k i : Fin 2) (x : LoopPlane) :=
    fderiv ℝ (F a i) (U x) (EuclideanSpace.single k 1, W k x)
  let DB (a : Fin n) (k : Fin 2) (x : LoopPlane) :=
    fderiv ℝ (B a) (U x) (EuclideanSpace.single k 1, W k x)
  let O : Set (LoopPlane × Jet n) :=
    {z | suJetBlock (0 : Fin 3) z.2 ∈ (extChartAt (𝓡 n) b).target}
  have hFs (a : Fin n) (i : Fin 2) : ContDiffOn ℝ 1 (F a i) O := by
    intro z hz
    have hf := (suAlphaJetOriginal_contDiffAt g b alpha (suAlphaFirstJetPoint z) hz).1
    exact (((hf.comp z suAlphaFirstJetPoint_contDiff.contDiffAt).clm_apply
      contDiffAt_const).of_le (by simp)).contDiffWithinAt
  have hBs (a : Fin n) : ContDiffOn ℝ 1 (B a) O := by
    intro z hz
    have hf := (suAlphaJetOriginal_contDiffAt g b alpha (suAlphaFirstJetPoint z) hz).2
    exact (((hf.comp z suAlphaFirstJetPoint_contDiff.contDiffAt).clm_apply
      contDiffAt_const).of_le (by simp)).contDiffWithinAt
  have hFd (a : Fin n) (i : Fin 2) := suFirstJet_coefficient_chain S G H hr hrH (hFs a i)
  have hBd (a : Fin n) := suFirstJet_coefficient_chain S G H hr hrH (hBs a)
  have hrH' : r < H.radius := hrH.trans (half_lt_self H.radius_pos)
  have hrG : r < G.radius := hrH'.trans H.radius_lt
  have hrR : r < R := hrG.trans G.radius_lt
  let mu := volume.restrict (ball center r)
  let : IsFiniteMeasure mu := ⟨by
    rw [Measure.restrict_apply_univ]
    exact measure_ball_lt_top⟩
  have hmu : mu ≤ volume.restrict (ball center rho) :=
    Measure.restrict_mono (ball_subset_ball hrH.le) le_rfl
  have hcol (i : Fin 2) : ∀ᵐ x ∂mu, fderiv ℝ u x (EuclideanSpace.single i 1) = V i x :=
    ae_restrict_of_ae_restrict_of_subset (ball_subset_ball hrH'.le) (H.column_ae i)
  have hsym (i j : Fin 2) : ∀ᵐ x ∂mu, G.hessian i j x = G.hessian j i x :=
    ae_restrict_of_ae_restrict_of_subset (ball_subset_ball hrG.le) (G.hessian_symm_ae i j)
  have hpoint : ∀ᵐ x ∂mu,
      suAlphaFirstJetPoint (U x) = ((x, u x), (V 0 x, V 1 x)) := by
    filter_upwards [hcol 0, hcol 1] with x h0 h1
    dsimp only [U, J, suAlphaFirstJetPoint]
    have hd0 : suJetBlock (1 : Fin 3) (suFirstJet u x) =
        fderiv ℝ u x (EuclideanSpace.single 0 1) := by
      simpa using suJetBlock_firstJet_succ u (0 : Fin 2) x
    have hd1 : suJetBlock (2 : Fin 3) (suFirstJet u x) =
        fderiv ℝ u x (EuclideanSpace.single 1 1) := by
      simpa using suJetBlock_firstJet_succ u (1 : Fin 2) x
    rw [suJetBlock_firstJet_zero, hd0, hd1]
    rw [h0, h1]
  have hFae (a : Fin n) (i : Fin 2) : ∀ᵐ x ∂mu, F a i (U x) = S.flux a i x := by
    filter_upwards [hpoint] with x hx
    dsimp only [F]
    rw [hx]
    change suAlphaCoordinateFlux g b alpha (x, u x) (V 0 x, V 1 x) _ = _
    rw [S.coordinateFlux_pairing]
    fin_cases i <;> simp [suColumnBasis]
  have hBae (a : Fin n) : ∀ᵐ x ∂mu, B a (U x) = S.sourceTerm a x := by
    filter_upwards [hpoint] with x hx
    dsimp only [B]
    rw [hx]
    change suAlphaCoordinateSource g b alpha (x, u x) (V 0 x, V 1 x) _ = _
    rw [S.coordinateSource_pairing]
    simp
  have heq (a : Fin n) (psi : LoopPlane → ℝ) (hpsi : ContDiff ℝ ∞ psi)
      (hpc : HasCompactSupport psi) (hps : tsupport psi ⊆ ball center r) :
      (∫ x in ball center r, ∑ i : Fin 2,
        F a i (U x) * fderiv ℝ psi x (EuclideanSpace.single i 1)) =
        ∫ x in ball center r, B a (U x) * psi x := by
    have he := S.indicator_equation ha hrR.le a hpsi hpc hps
    have he' : (∫ x in ball center r, ∑ i : Fin 2,
        S.flux a i x * fderiv ℝ psi x (EuclideanSpace.single i 1)) =
        ∫ x in ball center r, S.sourceTerm a x * psi x := by
      rw [← integral_indicator measurableSet_ball, ← integral_indicator measurableSet_ball]
      convert he using 1 <;> congr 1 <;> funext x <;>
        by_cases hx : x ∈ ball center r <;> simp [hx]
    calc
      _ = ∫ x in ball center r, ∑ i : Fin 2,
          S.flux a i x * fderiv ℝ psi x (EuclideanSpace.single i 1) := by
        apply integral_congr_ae
        filter_upwards [ae_all_iff.mpr (hFae a)] with x hx
        simp only [hx]
      _ = _ := he'
      _ = _ := integral_congr_ae ((hBae a).mono fun x hx => by rw [hx])
  have hFint (a : Fin n) (i : Fin 2) : IntegrableOn (fun x => F a i (U x)) (ball center r) :=
    ((hFd a i).1.mono_measure hmu).integrable (by norm_num)
  have hDFint (a : Fin n) (k i : Fin 2) : IntegrableOn (DF a k i) (ball center r) :=
    (((hFd a i).2 k).1.mono_measure hmu).integrable (by norm_num)
  obtain ⟨⟨j, a⟩, rfl⟩ := (finProdFinEquiv : Fin 3 × Fin n ≃ Fin (3 * n)).surjective a
  cases j using Fin.cases with
  | zero =>
    have hleft : ∀ᵐ x ∂mu, ∀ i : Fin 2,
        (suAlphaFirstJetCoefficients g b alpha).flux (U x) (W 0 x, W 1 x)
          (suColumnBasis (finProdFinEquiv ((0 : Fin 3), a)) i) = F a i (U x) := by
      filter_upwards [hpoint] with x hx i
      apply suAlphaFirstJet_flux_zero
      rw [hx]
      exact Prod.ext (suJetBlock_firstJetWeakColumn_zero V G.hessian 0 x)
        (suJetBlock_firstJetWeakColumn_zero V G.hessian 1 x)
    calc
      _ = ∫ x in ball center r, ∑ i : Fin 2,
          F a i (U x) * fderiv ℝ phi x (EuclideanSpace.single i 1) :=
        integral_congr_ae (hleft.mono fun x hx => by
          dsimp only [U, J, W] at hx
          simp only [U, J, hx])
      _ = ∫ x in ball center r, B a (U x) * phi x := heq a phi hp hc hs
      _ = _ := integral_congr_ae (Eventually.of_forall fun x => by
        rw [show (suAlphaFirstJetCoefficients g b alpha).source (U x) (W 0 x, W 1 x)
          (EuclideanSpace.single (finProdFinEquiv ((0 : Fin 3), a)) 1) = B a (U x) from
            suAlphaFirstJet_source_zero g b alpha (U x) (W 0 x, W 1 x) a])
  | succ k =>
    have hdir : ∀ᵐ x ∂mu,
        suAlphaFirstJetPoint (EuclideanSpace.single k 1, W k x) =
          ((EuclideanSpace.single k 1, suJetBlock k.succ (J x)),
            ((suJetBlock k.succ).prodMap (suJetBlock k.succ)) (W 0 x, W 1 x)) := by
      filter_upwards [hcol k, hsym 0 k, hsym 1 k] with x hk h0 h1
      dsimp only [suAlphaFirstJetPoint, W, J]
      have hd0 : suJetBlock (1 : Fin 3) (suFirstJetWeakColumn V G.hessian k x) =
          G.hessian 0 k x := by
        simpa using suJetBlock_firstJetWeakColumn_succ V G.hessian k (0 : Fin 2) x
      have hd1 : suJetBlock (2 : Fin 3) (suFirstJetWeakColumn V G.hessian k x) =
          G.hessian 1 k x := by
        simpa using suJetBlock_firstJetWeakColumn_succ V G.hessian k (1 : Fin 2) x
      rw [suJetBlock_firstJetWeakColumn_zero, hd0, hd1, suJetBlock_firstJet_succ]
      change ((EuclideanSpace.single k (1 : ℝ), V k x), (G.hessian 0 k x, G.hessian 1 k x)) =
        ((EuclideanSpace.single k 1, fderiv ℝ u x (EuclideanSpace.single k 1)),
          (suJetBlock k.succ (suFirstJetWeakColumn V G.hessian 0 x),
            suJetBlock k.succ (suFirstJetWeakColumn V G.hessian 1 x)))
      rw [suJetBlock_firstJetWeakColumn_succ, suJetBlock_firstJetWeakColumn_succ, hk, h0, h1]
    have hleft (i : Fin 2) : ∀ᵐ x ∂mu,
        (suAlphaFirstJetCoefficients g b alpha).flux (U x) (W 0 x, W 1 x)
          (suColumnBasis (finProdFinEquiv (k.succ, a)) i) = DF a k i x := by
      filter_upwards [hdir, ae_restrict_mem measurableSet_ball] with x hx hxr
      have hy : suJetBlock (0 : Fin 3) (J x) ∈ (extChartAt (𝓡 n) b).target := by
        rw [suJetBlock_firstJet_zero]
        exact S.coordinate_range (ball_subset_closedBall (ball_subset_ball hrR.le hxr))
      change suAlphaFirstJetFlux g b alpha (U x) (W 0 x, W 1 x) _ = _
      rw [suAlphaFirstJet_flux_succ g b alpha _ _ hy]
      dsimp only [DF, F]
      have hh := (suAlphaJetOriginal_contDiffAt g b alpha
        (suAlphaFirstJetPoint (U x)) hy).1.differentiableAt (by simp)
      rw [suFirstJet_scalar_fderiv hh, hx]
    have hright : ∀ᵐ x ∂mu,
        (suAlphaFirstJetCoefficients g b alpha).source (U x) (W 0 x, W 1 x)
          (EuclideanSpace.single (finProdFinEquiv (k.succ, a)) 1) = DB a k x := by
      filter_upwards [hdir, ae_restrict_mem measurableSet_ball] with x hx hxr
      have hy : suJetBlock (0 : Fin 3) (J x) ∈ (extChartAt (𝓡 n) b).target := by
        rw [suJetBlock_firstJet_zero]
        exact S.coordinate_range (ball_subset_closedBall (ball_subset_ball hrR.le hxr))
      change suAlphaFirstJetSource g b alpha (U x) (W 0 x, W 1 x) _ = _
      rw [suAlphaFirstJet_source_succ]
      dsimp only [DB, B]
      have hh := (suAlphaJetOriginal_contDiffAt g b alpha
        (suAlphaFirstJetPoint (U x)) hy).2.differentiableAt (by simp)
      rw [suFirstJet_scalar_fderiv hh, hx]
    calc
      _ = ∫ x in ball center r, ∑ i : Fin 2,
          DF a k i x * fderiv ℝ phi x (EuclideanSpace.single i 1) := by
        apply integral_congr_ae
        filter_upwards [ae_all_iff.mpr hleft] with x hx
        dsimp only [U, J, W] at hx
        simp only [hx]
      _ = ∫ x in ball center r, DB a k x * phi x :=
        suWeakDivergence_prolong k (hFint a) (hDFint a k)
          (fun i => ((hFd a i).2 k).2) ((hBd a).2 k).2 (heq a) hp hc hs
      _ = _ := integral_congr_ae (hright.mono fun x hx => by rw [hx])

theorem suWeakAlphaCoordinate_first_jet_system_coefficients
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (E n) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} {b : M} {alpha : ℝ}
    {u : LoopPlane → E n} {V : Fin 2 → LoopPlane → E n} {center : LoopPlane} {R : ℝ}
    (S : SUWeakAlphaCoordinate g b alpha u V center R) (ha : 1 ≤ alpha)
    (G : SUInitialGain u V center R) (H : SUC1HolderGain u V center G.radius) :
    ∃ r, 0 < r ∧ r < H.radius / 2 ∧
      ∃ T : SUQuadraticWeakSystem
        (suFirstJet u) (suFirstJetWeakColumn V G.hessian) center r,
        T.flux = (suAlphaFirstJetCoefficients g b alpha).flux ∧
          T.source = (suAlphaFirstJetCoefficients g b alpha).source := by
  let J := suFirstJet u
  let W := suFirstJetWeakColumn V G.hessian
  let rho := H.radius / 2
  have hrho : 0 < rho := half_pos H.radius_pos
  obtain ⟨hJ, _, hW, hw⟩ := suFirstJet_weak_data G H
  let O : Set (Jet n) := {y | suJetBlock (0 : Fin 3) y ∈ (extChartAt (𝓡 n) b).target}
  have hO : IsOpen O := (isOpen_extChartAt_target b).preimage (suJetBlock (0 : Fin 3)).continuous
  have hcenter : J center ∈ O := by
    change suJetBlock (0 : Fin 3) (suFirstJet u center) ∈ (extChartAt (𝓡 n) b).target
    rw [suJetBlock_firstJet_zero]
    exact S.coordinate_range (mem_closedBall_self S.radius_pos.le)
  obtain ⟨d, hd, hball⟩ := Metric.isOpen_iff.mp hO (J center) hcenter
  let delta := d / 2
  have hdelta : 0 < delta := half_pos hd
  have hclosed : closedBall (J center) delta ⊆ O :=
    (closedBall_subset_ball (half_lt_self hd)).trans hball
  let K := suJetBlock (0 : Fin 3) '' closedBall (J center) delta
  have hK : IsCompact K :=
    (isCompact_closedBall (J center) delta).image (suJetBlock (0 : Fin 3)).continuous
  have hKchart : K ⊆ (extChartAt (𝓡 n) b).target := by
    rintro _ ⟨y, hy, rfl⟩
    exact hclosed hy
  obtain ⟨kappa, _, hkappa, _, _, _, hmetric⟩ := suAlpha_coordinate_metric_bounds g b hK hKchart
  have hJat : ContinuousAt J center := hJ.continuousAt (closedBall_mem_nhds center hrho)
  obtain ⟨s, hs, hJs⟩ := Metric.continuousAt_iff.mp hJat (delta / 2) (half_pos hdelta)
  let r := min (rho / 2) (s / 2)
  have hr : 0 < r := lt_min (half_pos hrho) (half_pos hs)
  have hrrho : r < rho := (min_le_left _ _).trans_lt (half_lt_self hrho)
  have hrs : r < s := (min_le_right _ _).trans_lt (half_lt_self hs)
  have hrange : MapsTo J (closedBall center r) (ball (J center) (delta / 2)) := by
    intro x hx
    exact mem_ball.mpr (hJs ((mem_closedBall.mp hx).trans_lt hrs))
  have hcols (i : Fin 2) : MemLp (W i) 2 (volume.restrict (ball center r)) :=
    (hW i).mono_measure (Measure.restrict_mono (ball_subset_ball hrrho.le) le_rfl)
  have hweak (i : Fin 2) (a : Fin (3 * n)) :
      HasWeakPartialDeriv i (fun x => W i x a) (fun x => J x a) (ball center r) :=
    (hw i a).restrict isOpen_ball (ball_subset_ball hrrho.le)
  let C := suAlphaFirstJetCoefficients g b alpha
  have hsmooth (z : LoopPlane × Jet n)
      (hz : z ∈ closedBall center r ×ˢ closedBall (J center) delta) :=
    suAlphaFirstJet_coefficients_contDiffAt g b alpha z (hclosed hz.2)
  have hcoercive (z : LoopPlane × Jet n)
      (hz : z ∈ closedBall center r ×ˢ closedBall (J center) delta) (q : Grad (3 * n)) :
      (2 * kappa) * ‖q‖ ^ 2 ≤ C.principal z q q := by
    apply suJetBlockPrincipal_coercive (by positivity)
    intro v
    exact suAlphaCoordinateFlux_principal_coercive g b ha z.1
      (suJetBlock (0 : Fin 3) z.2) hkappa
      (hmetric _ (mem_image_of_mem _ hz.2)) (suAlphaFirstJetPoint z).2 v
  obtain ⟨T, hF, hB⟩ := suAffineQuadraticSystem C hr hdelta (by positivity : 0 < 2 * kappa)
    (hJ.mono (closedBall_subset_closedBall hrrho.le)) hcols hweak hrange
    (fun z hz => (hsmooth z hz).1.of_le (by simp))
    (fun z hz => (hsmooth z hz).2.1.of_le (by simp))
    (fun z hz => (hsmooth z hz).2.2.1.of_le (by simp))
    (fun z hz => (hsmooth z hz).2.2.2.of_le (by simp)) hcoercive
    (fun a phi hp hc hs => suWeakAlphaCoordinate_first_jet_equation S ha G H hr hrrho a hp hc hs)
  exact ⟨r, hr, hrrho, T, hF, hB⟩

theorem suWeakAlphaCoordinate_first_jet_system
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (E n) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} {b : M} {alpha : ℝ}
    {u : LoopPlane → E n} {V : Fin 2 → LoopPlane → E n} {center : LoopPlane} {R : ℝ}
    (S : SUWeakAlphaCoordinate g b alpha u V center R) (ha : 1 ≤ alpha)
    (G : SUInitialGain u V center R) (H : SUC1HolderGain u V center G.radius) :
    ∃ r, 0 < r ∧ r < H.radius / 2 ∧
      Nonempty (SUQuadraticWeakSystem
        (suFirstJet u) (suFirstJetWeakColumn V G.hessian) center r) := by
  obtain ⟨r, hr, hrH, T, _, _⟩ := suWeakAlphaCoordinate_first_jet_system_coefficients S ha G H
  exact ⟨r, hr, hrH, ⟨T⟩⟩

theorem suWeakAlphaCoordinate_first_jet_gain
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (E n) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} {b : M} {alpha : ℝ}
    {u : LoopPlane → E n} {V : Fin 2 → LoopPlane → E n} {center : LoopPlane} {R : ℝ}
    (S : SUWeakAlphaCoordinate g b alpha u V center R) (ha : 1 ≤ alpha)
    (G : SUInitialGain u V center R) (H : SUC1HolderGain u V center G.radius) :
    Nonempty (SUInitialGain (suFirstJet u) (suFirstJetWeakColumn V G.hessian)
      center (H.radius / 2)) := by
  obtain ⟨r, _, hr, ⟨T⟩⟩ := suWeakAlphaCoordinate_first_jet_system S ha G H
  obtain ⟨K⟩ := suQuadraticWeakSystem_initial_gain T
  exact ⟨{ K with radius_lt := K.radius_lt.trans hr }⟩

end PoincareConjecture.M60
