import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryCoordinateGram
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryQuadraticConformalC1
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundedCoordinateWeakChain
import PoincareConjecture.Proofs.M64.Mathlib.MeasurePreservingColumnEnergy

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric MeasureTheory
open scoped Topology Manifold ContDiff
open Poincare.Analysis.Sobolev.Weak

namespace PoincareConjecture

theorem m64RegularCurve_boundary_observed_contDiffOn {n m : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
    [IsManifold (𝓡 (n + 1)) ∞ M]
    (g : RiemannianMetric (n + 1) M)
    (e : M → EuclideanSpace ℝ (Fin m))
    (he : ContMDiff (𝓡 (n + 1)) (𝓡 m) ∞ e) (hei : Topology.IsEmbedding e)
    (hread : M60.SUChartReadable (n := n + 1) e)
    (C : ℝ → M) (hC : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 C)
    (hregular : curveVelocity (n := n + 1) C 0 ≠ 0)
    (B : M → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ)
    (hB : Continuous B) {bound : ℝ} (hb : ∀ q, ‖B q‖ ≤ bound)
    (hsymm : ∀ q v w, B q v w = B q w v) (hpos : ∀ q v, 0 ≤ B q v v)
    {Cm : ℝ} (hCm : 0 ≤ Cm)
    (hcoercive : ∀ (q : M) (v : EuclideanSpace ℝ (Fin m)),
      v ∈ range (mfderiv (𝓡 (n + 1)) (𝓡 m) e q) → ‖v‖ ^ 2 ≤ Cm * B q v v)
    (hdiag : ∀ (q : M) (v : TangentSpace (𝓡 (n + 1)) q),
      B q (mfderiv (𝓡 (n + 1)) (𝓡 m) e q v)
        (mfderiv (𝓡 (n + 1)) (𝓡 m) e q v) = g.inner q v v)
    (U : LoopPlane → EuclideanSpace ℝ (Fin m))
    (V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin m)) (f : LoopPlane → M)
    (ell : LoopPlane → ℝ) {rho C0 H0 beta Lambda : ℝ} (hrho : 0 < rho)
    (hU : ContinuousOn U (closedBall (0 : LoopPlane) (2 * rho)))
    (hV : ∀ i, MemLp (V i) 2 (volume.restrict (ball (0 : LoopPlane) (2 * rho))))
    (hweak : ∀ i j, HasWeakPartialDeriv i (fun z => V i z j) (fun z => U z j)
      (ball (0 : LoopPlane) (2 * rho)))
    (hsmooth : ContDiffOn ℝ 2 U (ball (0 : LoopPlane) (2 * rho) ∩ {z | 0 < z 1}))
    (hobs : EqOn U (e ∘ f) (ball (0 : LoopPlane) (2 * rho) ∩ {z | 0 < z 1}))
    (hell : ContinuousAt ell 0) (hell0 : ell 0 = 0)
    (htrace : ∀ z ∈ closedBall (0 : LoopPlane) rho, z 1 = 0 → U z = e (C (ell z)))
    (hconf : ∀ z ∈ ball (0 : LoopPlane) (2 * rho) ∩ {z | 0 < z 1},
      m60AreaGram g f z 0 0 = m60AreaGram g f z 1 1 ∧ m60AreaGram g f z 0 1 = 0)
    (hC0 : 0 ≤ C0) (hH0 : 0 ≤ H0) (hbeta : 0 < beta) (hLambda : 0 ≤ Lambda)
    (hgrowth : ∀ z ∈ ball (0 : LoopPlane) (2 * rho) ∩ {z | 0 < z 1},
      ‖∑ i : Fin 2, fderiv ℝ (fderiv ℝ U) z
        (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)‖ ≤
        C0 * ∑ i : Fin 2, ‖fderiv ℝ U z (EuclideanSpace.single i 1)‖ ^ 2)
    (hholder : ∀ x ∈ closedBall (0 : LoopPlane) rho,
      ∀ z ∈ closedBall (0 : LoopPlane) rho, ‖U z - U x‖ ≤ H0 * dist z x ^ beta)
    (henergy : ∀ x ∈ closedBall (0 : LoopPlane) (rho / 2),
      ∀ r : ℝ, 0 < r → r ≤ rho / 2 →
      (∫ z in closedBall x r, ∑ i : Fin 2, ‖V i z‖ ^ 2) ≤ Lambda * r ^ (2 * beta)) :
    ∃ r : ℝ, 0 < r ∧ r ≤ rho ∧
      ContDiffOn ℝ 1 U (closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1}) ∧
      ∃ F : LoopPlane → M,
        ContMDiffOn (𝓡 2) (𝓡 (n + 1)) 1 F
          (closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1}) ∧
        EqOn F f (ball (0 : LoopPlane) r ∩ {z | 0 < z 1}) ∧
        (∀ z ∈ closedBall (0 : LoopPlane) r, z 1 = 0 → F z = C (ell z)) ∧
        EqOn U (e ∘ F) (closedBall (0 : LoopPlane) r ∩ {z | 0 ≤ z 1}) := by
  obtain ⟨H, J, L, eps, delta, eta, K, heps, hdelta, heta, -, hK, hHcenter, -,
    hH, hLip, hHD, hJ, -, hright, hJD, hleft, haxis⟩ :=
      m64ChartReadable_bounded_C2_boundary_chart e he hei hread C hC hregular
        isOpen_univ (mem_univ _)
  let u := H ∘ U
  let W := fun i z => fderiv ℝ H (U z) (V i z)
  have hUcenter : U 0 = e (C 0) := by
    simpa only [hell0] using htrace 0 (mem_closedBall_self hrho.le) (by simp)
  have hucenter : u 0 = 0 := by simp only [u, Function.comp_apply, hUcenter, hHcenter]
  have hUa : ContinuousAt U 0 := hU.continuousAt (closedBall_mem_nhds _ (by positivity))
  have hua : ContinuousAt u 0 := hH.continuous.continuousAt.comp hUa
  have hnearU : ∀ᶠ z in 𝓝 (0 : LoopPlane), dist (U z) (e (C 0)) < delta := by
    have h := hUa.eventually (Metric.ball_mem_nhds (U 0) hdelta)
    simpa only [hUcenter, mem_ball] using h
  have hnearu : ∀ᶠ z in 𝓝 (0 : LoopPlane), ‖u z‖ < eps / 4 := by
    have h := hua.eventually (Metric.ball_mem_nhds (u 0) (by positivity : 0 < eps / 4))
    simpa only [hucenter, mem_ball, dist_zero_right] using h
  have hnearEll : ∀ᶠ z in 𝓝 (0 : LoopPlane), ell z ∈ Ioo (-eta) eta := by
    apply hell.eventually
    rw [hell0]
    exact Ioo_mem_nhds (by linarith) heta
  obtain ⟨rN, hrN, hN⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (hnearU.and (hnearu.and hnearEll))
  let R := min rN rho / 2
  have hR : 0 < R := half_pos (lt_min hrN hrho)
  have hRrho : R ≤ rho / 2 := by dsimp only [R]; linarith [min_le_right rN rho]
  have hRR : R < 2 * rho := by linarith only [hRrho, hrho]
  have hparams (z : LoopPlane) (hz : z ∈ closedBall 0 R) :
      dist (U z) (e (C 0)) < delta ∧ ‖u z‖ < eps / 4 ∧ ell z ∈ Ioo (-eta) eta := by
    exact hN (closedBall_subset_closedBall
      (by dsimp only [R]; linarith [min_le_left rN rho]) hz)
  have hcoord (z : LoopPlane) (hz : z ∈ closedBall 0 R) : u z ∈ closedBall 0 eps := by
    apply mem_closedBall.mpr
    rw [dist_zero_right]
    linarith only [(hparams z hz).2.1, heps]
  have hsmall : closedBall (0 : LoopPlane) R ⊆ closedBall 0 rho :=
    closedBall_subset_closedBall (by linarith only [hRrho, hrho])
  have hJball : closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) eps ⊆ ball 0 (2 * eps) :=
    closedBall_subset_ball (by linarith only [heps])
  let S : Set LoopPlane := ball 0 R ∩ {z | 0 < z 1}
  have hS : IsOpen S := isOpen_ball.inter (isOpen_lt continuous_const (by fun_prop))
  have hsub : S ⊆ ball (0 : LoopPlane) (2 * rho) ∩ {z | 0 < z 1} :=
    fun z hz => ⟨ball_subset_ball hRR.le hz.1, hz.2⟩
  have hus : ContDiffOn ℝ 2 u S := hH.comp_contDiffOn (hsmooth.mono hsub)
  have hucont : ContinuousOn u (closedBall (0 : LoopPlane) (2 * rho)) :=
    hH.continuous.comp_continuousOn hU
  have hJe : ContDiffOn ℝ 2 (e ∘ J) (ball 0 (2 * eps)) := by
    intro y hy
    exact (contMDiffAt_iff_contDiffAt.mp
      ((he.of_le (WithTop.coe_le_coe.mpr le_top)).contMDiffAt.comp y
        (hJ.contMDiffAt (isOpen_ball.mem_nhds hy)))).contDiffWithinAt
  have hrec (z : LoopPlane) (hz : z ∈ S) : J (u z) = f z := by
    have hzU := hobs (hsub hz)
    dsimp only [Function.comp_apply] at hzU
    have hclose : dist (e (f z)) (e (C 0)) < delta := by
      rw [← hzU]
      exact (hparams z (ball_subset_closedBall hz.1)).1
    simpa only [u, Function.comp_apply, hzU] using (hleft (f z) hclose).2
  have hrecgerm (z : LoopPlane) (hz : z ∈ S) : f =ᶠ[𝓝 z] J ∘ u := by
    filter_upwards [hS.mem_nhds hz] with y hy
    exact (hrec y hy).symm
  have hUrecgerm (z : LoopPlane) (hz : z ∈ S) : U =ᶠ[𝓝 z] (e ∘ J) ∘ u := by
    filter_upwards [hS.mem_nhds hz] with y hy
    exact (hobs (hsub hy)).trans (congrArg e (hrec y hy).symm)
  obtain ⟨huLp, hWLp, hWweak⟩ := m64BoundedCoordinate_weak_chain hR hRR hU hV hweak
    (hH.of_le (by norm_num)) hK (fun y => (hHD y).1)
  let G := fun z => m64ObservedCoordinateMetric (e ∘ J) (B ∘ J) (u z)
  obtain ⟨lower, upper, hlower, hupper, hGcont, hmetric⟩ :=
    m64BoundaryCoordinate_metric_data e (he.of_le (by simp)) J H heps hK
      (hJ.of_le (by norm_num)) (hH.of_le (by norm_num)) hright
      (fun y => (hHD y).1) hJD B hB hb hsymm hpos hCm hcoercive
  have hG : ContinuousOn G (closedBall (0 : LoopPlane) R ∩ {z | 0 ≤ z 1}) :=
    hGcont.comp (hucont.mono (fun z hz =>
      closedBall_subset_closedBall hRR.le hz.1)) (fun z hz => hcoord z hz.1)
  have hgram (z : LoopPlane) (hz : z ∈ S) (i j : Fin 2) :
      G z (fderiv ℝ u z (EuclideanSpace.single i 1))
        (fderiv ℝ u z (EuclideanSpace.single j 1)) = m60AreaGram g f z i j :=
    m64BoundaryCoordinate_metric_gram g e (he.of_le (by simp)) J B hsymm hdiag
      ((hus.contDiffAt (hS.mem_nhds hz)).differentiableAt (by norm_num))
      ((hJ.contMDiffAt (isOpen_ball.mem_nhds
        (hJball (hcoord z (ball_subset_closedBall hz.1))))).mdifferentiableAt (by norm_num))
      (hrecgerm z hz) i j
  have hqgrowth (z : LoopPlane) (hz : z ∈ S) :
      ‖∑ i : Fin 2, fderiv ℝ (fderiv ℝ u) z
        (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)‖ ≤
        ((K + K * C0) * K ^ 2) *
          ∑ i : Fin 2, ‖fderiv ℝ u z (EuclideanSpace.single i 1)‖ ^ 2 := by
    have hUz := (hsmooth.mono hsub).contDiffAt (hS.mem_nhds hz)
    have huz := (hus.contDiffAt (hS.mem_nhds hz)).differentiableAt (by norm_num)
    have hJz := (hJe.contDiffAt (isOpen_ball.mem_nhds
      (hJball (hcoord z (ball_subset_closedBall hz.1))))).differentiableAt (by norm_num)
    exact m64C2_coordinate_laplacian_growth hUz hH.contDiffAt
      (fun i => EuclideanSpace.single i 1) hC0 hK.le hK.le hK.le
      (hHD _).1 (hHD _).2 (hgrowth z (hsub hz))
      (fun i => m64C1_reconstruction_column_bound huz hJz (hUrecgerm z hz)
        (hJD _ (hcoord z (ball_subset_closedBall hz.1))) _)
  have hdecay (x : LoopPlane) (hx : x ∈ closedBall 0 (R / 4))
      (r : ℝ) (hr : 0 < r) (hrR : r ≤ R / 4) :
      (∫ z in closedBall x r, ∑ i : Fin 2, ‖W i z‖ ^ 2) ≤
        (K ^ 2 * Lambda) * r ^ (2 * beta) := by
    have hball : closedBall x r ⊆ ball (0 : LoopPlane) (2 * rho) := by
      intro z hz
      apply mem_ball.mpr
      linarith [mem_closedBall.mp hz, mem_closedBall.mp hx, dist_triangle z x (0 : LoopPlane)]
    have hcomp := m64MeasurePreserving_column_energy_le (MeasurePreserving.id volume)
      MeasurableEmbedding.id isClosed_closedBall.measurableSet (mapsTo_id _)
      V W (fun i => (hV i).mono_measure (Measure.restrict_mono_set volume hball))
      (fun i => (hWLp i).mono_measure (Measure.restrict_mono_set volume hball))
      (L := K) (fun i z _ => ((fderiv ℝ H (U z)).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (hHD _).1 (norm_nonneg _)))
    calc
      _ ≤ K ^ 2 * ∫ z in closedBall x r, ∑ i : Fin 2, ‖V i z‖ ^ 2 := hcomp
      _ ≤ K ^ 2 * (Lambda * r ^ (2 * beta)) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg K)
        exact henergy x (closedBall_subset_closedBall (by linarith) hx) r hr (by linarith)
      _ = _ := by ring
  have hC1 := m64Conformal_quadratic_boundary_contDiffOn hR u W
    (huLp.mono_measure (Measure.restrict_mono_set volume (ball_subset_ball hRR.le)))
    (fun i => (hWLp i).mono_measure
      (Measure.restrict_mono_set volume (ball_subset_ball hRR.le)))
    hWweak hus (hucont.mono (closedBall_subset_closedBall (by linarith)))
    (by positivity : 0 ≤ (K + K * C0) * K ^ 2)
    (mul_nonneg L.coe_nonneg hH0) hbeta (mul_nonneg (sq_nonneg K) hLambda)
    (fun x hx z hz => by
      have hx' := hsmall (closedBall_subset_closedBall (by linarith : R / 2 ≤ R) hx)
      have hz' := hsmall (closedBall_subset_closedBall (by linarith : R / 2 ≤ R) hz)
      exact (hLip.dist_le_mul (U z) (U x)).trans
        (mul_le_mul_of_nonneg_left (hholder x hx' z hz') L.coe_nonneg) |>.trans_eq (by ring))
    (0 : Fin (n + 1)) (fun z hz hz0 j hj => by
      have hzR := closedBall_subset_closedBall (by linarith : R / 2 ≤ R) hz
      have ht := htrace z (hsmall hzR) hz0
      have ha := (haxis (ell z) (hparams z hzR).2.2).1
      change H (U z) j = 0
      rw [ht, ha]
      simp [Ne.symm hj])
    G hG hlower hupper (fun z hz => hmetric _ (hcoord z hz.1))
    (fun z hz => by rw [hgram z hz 0 0, hgram z hz 1 1, hgram z hz 0 1]; exact hconf z (hsub hz))
    hqgrowth hdecay
  have hfinal : (closedBall (0 : LoopPlane) (R / 256) ∩ {z | 0 ≤ z 1}) ⊆
      closedBall (0 : LoopPlane) R :=
    fun z hz => closedBall_subset_closedBall (by linarith only [hR]) hz.1
  have hUrec (z : LoopPlane)
      (hz : z ∈ closedBall (0 : LoopPlane) (R / 256) ∩ {z | 0 ≤ z 1}) :
      U z = (e ∘ J) (u z) := by
    obtain ⟨q, hq⟩ : ∃ q : M, U z = e q := by
      by_cases hp : 0 < z 1
      · exact ⟨f z, hobs ⟨(closedBall_subset_ball hRR) (hfinal hz), hp⟩⟩
      · have hz0 : z 1 = 0 := le_antisymm (le_of_not_gt hp) hz.2
        exact ⟨C (ell z), htrace z (hsmall (hfinal hz)) hz0⟩
    have hclose : dist (e q) (e (C 0)) < delta := by
      rw [← hq]
      exact (hparams z (hfinal hz)).1
    change U z = e (J (H (U z)))
    rw [hq, (hleft q hclose).2]
  refine ⟨R / 256, by positivity, by linarith only [hRrho, hrho], ?_, J ∘ u, ?_, ?_, ?_,
    fun z hz => hUrec z hz⟩
  · exact ((hJe.of_le (by norm_num)).comp hC1
      (fun z hz => hJball (hcoord z (hfinal hz)))).congr hUrec
  · exact (hJ.of_le (by norm_num)).comp hC1.contMDiffOn
      (fun z hz => hJball (hcoord z (hfinal hz)))
  · intro z hz
    exact hrec z ⟨ball_subset_ball (by linarith only [hR] : R / 256 ≤ R) hz.1, hz.2⟩
  · intro z hz hz0
    have hzK : z ∈ closedBall (0 : LoopPlane) (R / 256) ∩ {z | 0 ≤ z 1} :=
      ⟨hz, hz0.ge⟩
    exact hei.injective ((hUrec z hzK).symm.trans (htrace z (hsmall (hfinal hzK)) hz0))

end PoincareConjecture
