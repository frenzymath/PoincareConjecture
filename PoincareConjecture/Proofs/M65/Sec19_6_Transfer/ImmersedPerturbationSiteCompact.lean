import PoincareConjecture.Proofs.M65.Sec19_6_Transfer.ImmersedPerturbationFiniteControls











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Metric
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M65Perturbation

local notation "ang" => (fun x : ℝ =>
  (Subtype.mk (Proofs.M58.angularPoint x) (Proofs.M58.norm_angularPoint x) : LoopCircle))



def angularSiteBox (K : Set ℝ) : Set LoopAmbient :=
  {z | z 0 ∈ Icc 0 rampPeriod ∧ z 1 ∈ Icc 0 rampPeriod ∧ z 2 ∈ K}



theorem angularSiteBox_compact (K : Set ℝ) (hK : IsCompact K) :
    IsCompact (angularSiteBox K) := by
  let f : (ℝ × ℝ) × ℝ → LoopAmbient := fun z => WithLp.toLp 2 ![z.1.1, z.1.2, z.2]
  have hf : Continuous f :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.continuous.comp
    (continuous_pi (fun i => by
      fin_cases i
      · exact continuous_fst.fst
      · exact continuous_fst.snd
      · exact continuous_snd))
  have himage : f '' ((Icc 0 rampPeriod ×ˢ Icc 0 rampPeriod) ×ˢ K) = angularSiteBox K := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨hw.1.1, hw.1.2, hw.2⟩
    · intro hz
      refine ⟨((z 0, z 1), z 2), ⟨⟨hz.1, hz.2.1⟩, hz.2.2⟩, ?_⟩
      ext i
      fin_cases i <;> rfl
  rw [← himage]
  exact ((isCompact_Icc.prod isCompact_Icc).prod hK).image hf




theorem angularSiteBox_lift (K : Set ℝ) (x y : LoopCircle) (t : ℝ) (ht : t ∈ K) :
    ∃ z ∈ angularSiteBox K, loopSite z = ((x, y), t) := by
  obtain ⟨u, hu, hux⟩ := Proofs.M58.exists_angularPoint x
  obtain ⟨v, hv, hvy⟩ := Proofs.M58.exists_angularPoint y
  refine ⟨WithLp.toLp 2 ![u, v, t], ⟨hu, hv, ht⟩, ?_⟩
  change ((ang u, ang v), t) = ((x, y), t)
  rw [show ang u = x from Subtype.ext hux, show ang v = y from Subtype.ext hvy]

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {M : Type u} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
  [IsManifold (𝓡 3) ∞ M]




theorem site_value_contMDiffAt (Gamma : P → ℝ → C1FreeLoopSpace (M := M))
    (J : Set ℝ) (d : ℝ) (hJ : IsOpen J)
    (hGamma : ContMDiffOn 𝓘(ℝ, P × (ℝ × ℝ)) (𝓡 3) ∞
      (fun w => periodicFreeLoop (Gamma w.1 w.2.2) w.2.1) (ball 0 d ×ˢ (univ ×ˢ J)))
    (w : P × LoopAmbient) (hp : w.1 ∈ ball 0 d) (ht : w.2 2 ∈ J) (i : Fin 3) :
    ContMDiffAt 𝓘(ℝ, P × LoopAmbient) (𝓡 3) ∞
      (fun z => periodicFreeLoop (Gamma z.1 (z.2 2)) (z.2 i)) w := by
  have hselect : ContDiff ℝ ∞ (fun z : P × LoopAmbient => (z.1, (z.2 i, z.2 2))) :=
    contDiff_fst.prodMk (((EuclideanSpace.proj i : LoopAmbient →L[ℝ] ℝ).contDiff.comp
      contDiff_snd).prodMk
        ((EuclideanSpace.proj 2 : LoopAmbient →L[ℝ] ℝ).contDiff.comp contDiff_snd))
  exact (hGamma.contMDiffAt ((isOpen_ball.prod (isOpen_univ.prod hJ)).mem_nhds
    ⟨hp, mem_univ _, ht⟩)).comp w hselect.contMDiff.contMDiffAt

variable [T2Space M]

set_option maxHeartbeats 600000 in





theorem exists_site_zero_capture (Gamma : P → ℝ → C1FreeLoopSpace (M := M))
    (J : Set ℝ) (d : ℝ) (hJ : IsOpen J) (hd : 0 < d)
    (hGamma : ContMDiffOn 𝓘(ℝ, P × (ℝ × ℝ)) (𝓡 3) ∞
      (fun w => periodicFreeLoop (Gamma w.1 w.2.2) w.2.1) (ball 0 d ×ˢ (univ ×ˢ J)))
    (S : Set LoopAmbient) (hS : IsCompact S) (hSJ : ∀ z ∈ S, z 2 ∈ J)
    (O : Set (P × LoopAmbient)) (hO : IsOpen O)
    (hcover : ∀ z ∈ S, periodicFreeLoop (Gamma 0 (z 2)) (z 0) =
      periodicFreeLoop (Gamma 0 (z 2)) (z 1) → (0, z) ∈ O) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ d ∧
      ∀ p ∈ ball 0 delta, ∀ z ∈ S, periodicFreeLoop (Gamma p (z 2)) (z 0) =
        periodicFreeLoop (Gamma p (z 2)) (z 1) → (p, z) ∈ O := by
  have hevent : ∀ z ∈ S, ∀ᶠ w : P × LoopAmbient in 𝓝 (0, z),
      periodicFreeLoop (Gamma w.1 (w.2 2)) (w.2 0) =
        periodicFreeLoop (Gamma w.1 (w.2 2)) (w.2 1) → w ∈ O := by
    intro z hz
    by_cases hzo : (0, z) ∈ O
    · filter_upwards [hO.mem_nhds hzo] with w hw
      exact fun _ => hw
    · have hc0 := (site_value_contMDiffAt Gamma J d hJ hGamma (0, z)
        (mem_ball_self hd) (hSJ z hz) 0).continuousAt
      have hc1 := (site_value_contMDiffAt Gamma J d hJ hGamma (0, z)
        (mem_ball_self hd) (hSJ z hz) 1).continuousAt
      have hne : periodicFreeLoop (Gamma 0 (z 2)) (z 0) ≠
          periodicFreeLoop (Gamma 0 (z 2)) (z 1) := fun h => hzo (hcover z hz h)
      filter_upwards [(hc0.ne_iff_eventually_ne hc1).mp hne] with w hw
      exact fun h => (hw h).elim
  have hall := hS.eventually_forall_of_forall_eventually (x₀ := (0 : P))
    (P := fun p z => periodicFreeLoop (Gamma p (z 2)) (z 0) =
      periodicFreeLoop (Gamma p (z 2)) (z 1) → (p, z) ∈ O) hevent
  obtain ⟨eps, heps, hepsO⟩ := Metric.mem_nhds_iff.mp hall
  exact ⟨min eps d, lt_min heps hd, min_le_right _ _,
    fun p hp => hepsO (ball_subset_ball (min_le_left _ _) hp)⟩




theorem compact_site_collisions [ProperSpace P]
    (Gamma : P → ℝ → C1FreeLoopSpace (M := M)) (J K : Set ℝ) (d r rho : ℝ)
    (hJ : IsOpen J) (hrd : r < d) (hK : IsCompact K) (hKJ : K ⊆ J)
    (hGamma : ContMDiffOn 𝓘(ℝ, P × (ℝ × ℝ)) (𝓡 3) ∞
      (fun w => periodicFreeLoop (Gamma w.1 w.2.2) w.2.1) (ball 0 d ×ˢ (univ ×ˢ J))) :
    IsCompact {w : P × LoopAmbient | w.1 ∈ closedBall 0 r ∧ w.2 ∈ angularSiteBox K ∧
      rho ≤ dist (ang (w.2 0)) (ang (w.2 1)) ∧
      periodicFreeLoop (Gamma w.1 (w.2 2)) (w.2 0) =
        periodicFreeLoop (Gamma w.1 (w.2 2)) (w.2 1)} := by
  let S : Set (P × LoopAmbient) := closedBall 0 r ×ˢ angularSiteBox K
  have hS : IsCompact S := (isCompact_closedBall (0 : P) r).prod (angularSiteBox_compact K hK)
  have hc (i : Fin 3) : ContinuousOn
      (fun w : P × LoopAmbient => periodicFreeLoop (Gamma w.1 (w.2 2)) (w.2 i)) S := by
    intro w hw
    exact (site_value_contMDiffAt Gamma J d hJ hGamma w
      (closedBall_subset_ball hrd hw.1) (hKJ hw.2.2.2) i).continuousAt.continuousWithinAt
  have hang (i : Fin 3) : Continuous (fun w : P × LoopAmbient => ang (w.2 i)) :=
    (Proofs.M58.contDiff_angularPoint.continuous.comp
      ((EuclideanSpace.proj i : LoopAmbient →L[ℝ] ℝ).continuous.comp continuous_snd)).subtype_mk _
  have hsep : IsClosed {w : P × LoopAmbient | rho ≤ dist (ang (w.2 0)) (ang (w.2 1))} :=
    isClosed_le continuous_const ((hang 0).dist (hang 1))
  have heq := hS.isClosed.isClosed_eq (hc 0) (hc 1)
  have hcompact := (hS.of_isClosed_subset heq (fun _ hw => hw.1)).inter_right hsep
  convert hcompact using 1
  ext w
  simp only [S, mem_inter_iff, mem_ofPred_eq, mem_prod]
  tauto

end PoincareConjecture.M65Perturbation
