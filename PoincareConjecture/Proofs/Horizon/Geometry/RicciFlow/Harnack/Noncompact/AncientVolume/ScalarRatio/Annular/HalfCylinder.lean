import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Annular.ClosedCompactness









set_option autoImplicit false

open Set Filter Metric
open scoped Topology ContDiff

namespace Poincare.AncientVolume

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [FiniteDimensional ℝ Y]



theorem exists_smooth_subsequence_on_ancient_halfCylinder
    {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R) (f : ℕ → ℝ × X → Y)
    (hf : ∀ j, ContDiffOn ℝ ∞ (f j) (Iic 0 ×ˢ ball 0 R))
    (hbound : ∀ a : ℝ, 0 < a → ∀ m : ℕ, ∃ B : ℝ, 0 ≤ B ∧
      ∀ j t, t ∈ Ioo (-a) 0 → ∀ x ∈ closedBall (0 : X) ρ,
        ‖iteratedFDeriv ℝ m (f j) (t, x)‖ ≤ B) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ F : ℝ × X → Y,
      ContDiffOn ℝ ∞ F (Iic 0 ×ˢ closedBall 0 ρ) ∧
      ∀ m K, IsCompact K → K ⊆ Iic 0 ×ˢ closedBall (0 : X) ρ →
        TendstoUniformlyOn
          (fun j => iteratedFDerivWithin ℝ m (f (σ j)) (Iic 0 ×ˢ closedBall 0 ρ))
          (iteratedFDerivWithin ℝ m F (Iic 0 ×ˢ closedBall 0 ρ)) atTop K := by
  let Ω : Set (ℝ × X) := Iic 0 ×ˢ closedBall 0 ρ
  have hclosed : IsClosed Ω := isClosed_Iic.prod isClosed_closedBall
  have hconvex : Convex ℝ Ω := (convex_Iic 0).prod (convex_closedBall 0 ρ)
  have hne : (interior Ω).Nonempty := by
    rw [show Ω = Iic 0 ×ˢ closedBall (0 : X) ρ from rfl,
      interior_prod_eq, interior_Iic, interior_closedBall (0 : X) hρ.ne']
    exact ⟨(-1, 0), by simp [hρ]⟩
  have hunique := uniqueDiffOn_convex hconvex hne
  have hΩ : Ω ⊆ Iic 0 ×ˢ ball (0 : X) R :=
    prod_mono subset_rfl (closedBall_subset_ball hρR)
  have hfs (j : ℕ) : ContDiffOn ℝ ∞ (f j) Ω := (hf j).mono hΩ
  apply exists_smooth_subsequence_on_closed_convex hclosed hconvex hne f hfs
  intro K hK hKΩ m
  obtain ⟨b, hb⟩ := hK.exists_bound_of_continuousOn
    (continuous_fst.continuousOn : ContinuousOn (fun z : ℝ × X => z.1) K)
  let a := max b 0 + 1
  have ha : 0 < a := by dsimp [a]; linarith [le_max_right b 0]
  obtain ⟨B, hB, hBbound⟩ := hbound a ha m
  refine ⟨B, hB, fun j z hz => ?_⟩
  let U : Set (ℝ × X) := Ioo (-a) 0 ×ˢ ball 0 ρ
  have hUo : IsOpen U := isOpen_Ioo.prod isOpen_ball
  have hUΩ : U ⊆ Ω := prod_mono (fun t ht => ht.2.le) ball_subset_closedBall
  have hzclosure : z ∈ closure U := by
    rw [show U = Ioo (-a) 0 ×ˢ ball (0 : X) ρ from rfl, closure_prod_eq,
      closure_Ioo (by linarith : -a ≠ 0), closure_ball (0 : X) hρ.ne']
    refine ⟨⟨?_, (hKΩ hz).1⟩, (hKΩ hz).2⟩
    have hbz : -b ≤ z.1 := (abs_le.mp (by simpa only [Real.norm_eq_abs] using hb z hz)).1
    dsimp [a]
    linarith [le_max_left b 0]
  have hm : (m : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr (le_top : (m : ℕ∞) ≤ ⊤)
  apply ContinuousWithinAt.closure_le hzclosure
    (((hfs j).continuousOn_iteratedFDerivWithin hm hunique z (hKΩ hz)).norm.mono hUΩ)
    continuousWithinAt_const
  intro y hy
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hunique
    (((hfs j).contDiffAt (mem_of_superset (hUo.mem_nhds hy) hUΩ)).of_le hm) (hUΩ hy)]
  exact hBbound j y.1 hy.1 y.2 (ball_subset_closedBall hy.2)

end Poincare.AncientVolume
