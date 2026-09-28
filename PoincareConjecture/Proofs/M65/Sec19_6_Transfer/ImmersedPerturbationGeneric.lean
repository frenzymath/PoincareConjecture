import PoincareConjecture.Proofs.M65.Sec19_6_Transfer.ImmersedPerturbationTransverse
import PoincareConjecture.Proofs.M65.Sec19_6_Transfer.ImmersedPerturbationFiniteFibers











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M65Perturbation

local notation "ang" => (fun x : ℝ =>
  (Subtype.mk (Proofs.M58.angularPoint x) (Proofs.M58.norm_angularPoint x) : LoopCircle))

variable {M : Type u} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M] [CompactSpace M]
  {a b : ℝ} {F : RicciFlow 3 M (Icc a b)} {J : Set ℝ}

omit [T2Space M] [CompactSpace M] in
private theorem original_separation_radius (C : M65SmoothFilledLoopFamily F J)
    (hJ : IsOpen J) (K : Set ℝ) (hK : IsCompact K) (hKJ : K ⊆ J) :
    ∃ rho : ℝ, 0 < rho ∧ ∀ t ∈ K, ∀ x y : LoopCircle,
      dist x y < rho → C.loops t x = C.loops t y → x = y := by
  let Gamma : ℝ → ℝ → C1FreeLoopSpace (M := M) := fun _ => C.loops
  have hGamma : ContMDiffOn 𝓘(ℝ, (ℝ × ℝ) × ℝ) (𝓡 3) 1
      (fun z => periodicFreeLoop (Gamma z.1.2 z.2) z.1.1)
      ((univ ×ˢ ball 0 1) ×ˢ J) :=
    (C.joint_smooth.of_le (by simp)).comp
      (contDiff_fst.fst.prodMk contDiff_snd).contMDiff.contMDiffOn
      (fun _ hz => ⟨mem_univ _, hz.2⟩)
  obtain ⟨d, rho, hd, _hd1, hrho, hcontrol⟩ :=
    exists_uniform_immersion_separation Gamma J K 1 hJ one_pos hK hKJ hGamma
      (fun t ht => C.immersed t (hKJ ht))
  exact ⟨rho, hrho, fun t ht => (hcontrol 0 (mem_ball_self hd) t ht).2⟩

set_option maxHeartbeats 1800000 in






theorem exists_generic_control_family (C : M65SmoothFilledLoopFamily F J)
    (hJ : IsOpen J) (K : Set ℝ) (hK : IsCompact K) (hKJ : K ⊆ J) :
    ∃ (N : ℕ) (delta : ℝ) (Gamma : (Fin N → ℝ) → ℝ → C1FreeLoopSpace (M := M))
        (Bad : Set (Fin N → ℝ)),
      0 < delta ∧
      ContMDiffOn 𝓘(ℝ, (Fin N → ℝ) × (ℝ × ℝ)) (𝓡 3) ∞
        (fun w => periodicFreeLoop (Gamma w.1 w.2.2) w.2.1) (ball 0 delta ×ˢ (univ ×ˢ J)) ∧
      (∀ t ∈ J, ∀ x, periodicFreeLoop (Gamma 0 t) x = periodicFreeLoop (C.loops t) x) ∧
      (∀ p ∈ ball 0 delta, ∀ t ∈ K, ∀ x,
        curveVelocity (n := 3) (periodicFreeLoop (Gamma p t)) x ≠ 0) ∧
      volume Bad = 0 ∧ ∀ p ∈ ball 0 delta, p ∉ Bad →
        {t | t ∈ K ∧ ¬Function.Injective (Gamma p t : LoopCircle → M)}.Finite := by
  classical
  obtain ⟨rho0, hrho0, hsep0⟩ := original_separation_radius C hJ K hK hKJ
  obtain ⟨k, d, Gamma, q, O, hd, hO, hGamma, hbase, hcover, hregular⟩ :=
    exists_transverse_control_family C hJ K hK hKJ (rho0 / 2) (half_pos hrho0)
  have hGammaSwap : ContMDiffOn 𝓘(ℝ, (ℝ × (Fin (k * 3) → ℝ)) × ℝ) (𝓡 3) 1
      (fun z => periodicFreeLoop (Gamma z.1.2 z.2) z.1.1) ((univ ×ˢ ball 0 d) ×ˢ J) :=
    (hGamma.of_le (by simp)).comp
      (contDiff_fst.snd.prodMk (contDiff_fst.fst.prodMk contDiff_snd)).contMDiff.contMDiffOn
      (fun _ hz => ⟨hz.1.2, mem_univ _, hz.2⟩)
  have hbaseRegular (t : ℝ) (ht : t ∈ K) (x : ℝ) :
      curveVelocity (n := 3) (periodicFreeLoop (Gamma 0 t)) x ≠ 0 := by
    rw [show periodicFreeLoop (Gamma 0 t) = periodicFreeLoop (C.loops t) from
      funext (hbase t (hKJ ht))]
    exact C.immersed t (hKJ ht) x
  obtain ⟨d1, rho1, hd1, hd1d, hrho1, hsep1⟩ :=
    exists_uniform_immersion_separation Gamma J K d hJ hd hK hKJ hGammaSwap hbaseRegular
  let rho := min rho1 (rho0 / 2)
  have hrho : 0 < rho := lt_min hrho1 (half_pos hrho0)
  let S : Set LoopAmbient := angularSiteBox K ∩
    {z | rho ≤ dist (ang (z 0)) (ang (z 1))}
  have hang (i : Fin 3) : Continuous (fun z : LoopAmbient => ang (z i)) :=
    (Proofs.M58.contDiff_angularPoint.continuous.comp
      (EuclideanSpace.proj i : LoopAmbient →L[ℝ] ℝ).continuous).subtype_mk _
  have hS : IsCompact S := (angularSiteBox_compact K hK).inter_right
    (isClosed_le continuous_const ((hang 0).dist (hang 1)))
  have hcoverS (z : LoopAmbient) (hz : z ∈ S)
      (heq : periodicFreeLoop (Gamma 0 (z 2)) (z 0) =
        periodicFreeLoop (Gamma 0 (z 2)) (z 1)) : (0, z) ∈ O := by
    have ht : z 2 ∈ K := hz.1.2.2
    have heqC : periodicFreeLoop (C.loops (z 2)) (z 0) =
        periodicFreeLoop (C.loops (z 2)) (z 1) := by
      simpa only [hbase (z 2) (hKJ ht)] using heq
    have hcircle : C.loops (z 2) (ang (z 0)) = C.loops (z 2) (ang (z 1)) :=
      ((C.loops (z 2)).boundary (ang (z 0))).symm.trans
        (heqC.trans ((C.loops (z 2)).boundary (ang (z 1))))
    have hfar : rho0 ≤ dist (ang (z 0)) (ang (z 1)) := by
      by_contra hn
      have hsame := hsep0 (z 2) ht _ _ (lt_of_not_ge hn) hcircle
      have hs : rho ≤ dist (ang (z 0)) (ang (z 1)) := hz.2
      rw [hsame, dist_self] at hs
      exact (not_le_of_gt hrho) hs
    exact hcover z ht ((half_le_self hrho0.le).trans hfar) heqC
  obtain ⟨dc, hdc, hdcd, hcapture⟩ := exists_site_zero_capture Gamma J d hJ hd hGamma
    S hS (fun z hz => hKJ hz.1.2.2) O hO hcoverS
  let r := min d1 dc / 2
  have hr : 0 < r := half_pos (lt_min hd1 hdc)
  have hrd1 : r < d1 := (half_lt_self (lt_min hd1 hdc)).trans_le (min_le_left _ _)
  have hrdc : r < dc := (half_lt_self (lt_min hd1 hdc)).trans_le (min_le_right _ _)
  have hrd : r < d := hrdc.trans_le hdcd
  let Z : Set ((Fin (k * 3) → ℝ) × LoopAmbient) :=
    {w | w.1 ∈ closedBall 0 r ∧ w.2 ∈ angularSiteBox K ∧
      rho ≤ dist (ang (w.2 0)) (ang (w.2 1)) ∧
      periodicFreeLoop (Gamma w.1 (w.2 2)) (w.2 0) =
        periodicFreeLoop (Gamma w.1 (w.2 2)) (w.2 1)}
  have hZ : IsCompact Z := compact_site_collisions Gamma J K d r rho hJ hrd hK hKJ hGamma
  have hzero (q0 : M) (w : Z) : loopDoublePointEquation Gamma q0 w.1 = 0 := by
    simp only [loopDoublePointEquation, w.2.2.2.2, sub_self]
  have hchart (w : Z) :
      ∃ (U : Set (Fin (k * 3) → ℝ)) (W : Set ((Fin (k * 3) → ℝ) × LoopAmbient))
          (phi : (Fin (k * 3) → ℝ) → (Fin (k * 3) → ℝ) × LoopAmbient)
          (coordinate : (Fin (k * 3) → ℝ) × LoopAmbient → (Fin (k * 3) → ℝ)),
        IsOpen U ∧ IsOpen W ∧ w.1 ∈ W ∧ ContDiffOn ℝ 1 phi U ∧ Continuous coordinate ∧
        ∀ z ∈ Z, z ∈ W → coordinate z ∈ U ∧ phi (coordinate z) = z := by
    have hwO : w.1 ∈ O := hcapture w.1.1 (closedBall_subset_ball hrdc w.2.1)
      w.1.2 ⟨w.2.2.1, w.2.2.2.1⟩ w.2.2.2.2
    obtain ⟨i, hQ, hB⟩ := hregular w.1 hwO
    obtain ⟨U, W, phi, coordinate, hU, hW, hwW, hphi, hc, _hforward, hback⟩ :=
      exists_control_zero_chart i (loopDoublePointEquation Gamma (q i)) w.1 hQ (hzero (q i) w) hB
    exact ⟨U, W, phi, coordinate, hU, hW, hwW, hphi, hc,
      fun z hz hzW => hback z hzW (hzero (q i) ⟨z, hz⟩)⟩
  choose U W phi coordinate hU hW hwW hphi hc hback using hchart
  obtain ⟨Bad, hBad, hfinite⟩ := finite_fibers_of_zero_charts volume Z hZ Prod.fst
    continuous_fst.continuousOn U W (fun i v => (phi i v).1) coordinate phi hU hW
    (fun i => (hphi i).fst) (fun i => (hc i).continuousOn)
    (fun z hz => mem_iUnion.mpr ⟨⟨z, hz⟩, hwW ⟨z, hz⟩⟩)
    (fun i z hz hzW => by
      obtain ⟨hmem, hinv⟩ := hback i z hz hzW
      exact ⟨hmem, congrArg Prod.fst hinv, hinv⟩)
  refine ⟨k * 3, r, Gamma, Bad, hr,
    hGamma.mono (prod_mono (ball_subset_ball hrd.le) Subset.rfl), hbase,
    fun p hp t ht => (hsep1 p (ball_subset_ball hrd1.le hp) t ht).1, hBad, ?_⟩
  intro p hp hpBad
  apply ((hfinite p hpBad).image (fun w => w.2 2)).subset
  intro t ht
  obtain ⟨x, y, heq, hxy⟩ := Function.not_injective_iff.mp ht.2
  have hfar : rho ≤ dist x y := by
    apply (min_le_left _ _).trans
    by_contra hn
    exact hxy ((hsep1 p (ball_subset_ball hrd1.le hp) t ht.1).2 x y (lt_of_not_ge hn) heq)
  obtain ⟨z, hz, hsite⟩ := angularSiteBox_lift K x y t ht.1
  have hzx : ang (z 0) = x := congrArg (fun w => w.1.1) hsite
  have hzy : ang (z 1) = y := congrArg (fun w => w.1.2) hsite
  have hzt : z 2 = t := congrArg Prod.snd hsite
  have hzfar : rho ≤ dist (ang (z 0)) (ang (z 1)) := by simpa only [hzx, hzy] using hfar
  have hzEq : periodicFreeLoop (Gamma p (z 2)) (z 0) =
      periodicFreeLoop (Gamma p (z 2)) (z 1) := by
    calc
      _ = Gamma p (z 2) (ang (z 0)) := (Gamma p (z 2)).boundary (ang (z 0))
      _ = Gamma p (z 2) (ang (z 1)) := by simpa only [hzt, hzx, hzy] using heq
      _ = _ := ((Gamma p (z 2)).boundary (ang (z 1))).symm
  exact ⟨(p, z), ⟨⟨ball_subset_closedBall hp, hz, hzfar, hzEq⟩, rfl⟩, hzt⟩

end PoincareConjecture.M65Perturbation
