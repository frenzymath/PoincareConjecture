import PoincareConjecture.Proofs.M65.Sec19_6_Transfer.ImmersedPerturbationSequence
import PoincareConjecture.Proofs.M65.Sec19_6_Transfer.ImmersedPerturbationBounds










set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M65Perturbation

variable {N : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M] {a b : ℝ} {J : Set ℝ}





theorem exists_controlled_generic_parameters (F : RicciFlow 3 M (Icc a b))
    (hJ : IsOpen J) (hJF : J ⊆ Ioo a b) (C : M65SmoothFilledLoopFamily F J)
    (Gamma : (Fin N → ℝ) → ℝ → C1FreeLoopSpace (M := M))
    (delta : ℝ) (hdelta : 0 < delta) (Bad : Set (Fin N → ℝ)) (hBad : volume Bad = 0)
    (hGamma : ContMDiffOn 𝓘(ℝ, (Fin N → ℝ) × (ℝ × ℝ)) (𝓡 3) ∞
      (fun z => periodicFreeLoop (Gamma z.1 z.2.2) z.2.1) (ball 0 delta ×ˢ (univ ×ˢ J)))
    (himm : ∀ p ∈ ball 0 delta, ∀ q ∈ J, ∀ x,
      curveVelocity (n := 3) (periodicFreeLoop (Gamma p q)) x ≠ 0)
    (hbase : ∀ q ∈ J, ∀ x, periodicFreeLoop (Gamma 0 q) x = periodicFreeLoop (C.loops q) x)
    (hCSF : ∀ q ∈ J, ∀ x,
      curveVelocity (n := 3) (fun t => periodicFreeLoop (C.loops t) x) q =
        m62CurvatureVector F (fun y t => periodicFreeLoop (C.loops t) y) q x)
    (K : Set ℝ) (hK : IsCompact K) (hKJ : K ⊆ J) :
    ∃ (p : ℕ → (Fin N → ℝ)) (L : ℝ), Tendsto p atTop (𝓝 0) ∧ 0 ≤ L ∧
      ∀ n, p n ∈ ball 0 delta ∧ p n ∉ Bad ∧
        (∀ q ∈ K, ∀ x,
          (F.metric q).tangentNorm (periodicFreeLoop (Gamma (p n) q) x)
            (curveVelocity (n := 3) (fun t => periodicFreeLoop (Gamma (p n) t) x) q -
              m62CurvatureVector F (fun y t => periodicFreeLoop (Gamma (p n) t) y) q x) ≤
                1 / ((n : ℝ) + 1)) ∧
        ∀ q ∈ K, freeLoopLength (F.metric q) (Gamma (p n) q) ≤ L := by
  obtain ⟨etaL, L, hetaL, hetaLdelta, hL, hlength⟩ := exists_uniform_length_bound F hJ hJF
    Gamma delta hdelta hGamma himm K hK hKJ
  have hradius (n : ℕ) := exists_uniform_residual_radius F hJ hJF C Gamma delta hdelta
    hGamma himm hbase hCSF K hK hKJ (1 / ((n : ℝ) + 1)) (by positivity)
  choose eta heta hetadelta hresidual using hradius
  obtain ⟨p, hp, hplim⟩ := exists_generic_parameter_sequence Bad hBad etaL hetaL eta heta
  have hpL (n : ℕ) : p n ∈ ball 0 etaL := by
    simpa only [mem_ball, dist_zero_right] using (hp n).1.trans_le (min_le_left _ _)
  have hpR (n : ℕ) : p n ∈ ball 0 (eta n) := by
    simpa only [mem_ball, dist_zero_right] using
      (hp n).1.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  refine ⟨p, L, hplim, hL, ?_⟩
  intro n
  exact ⟨ball_subset_ball hetaLdelta (hpL n), (hp n).2,
    hresidual n (p n) (hpR n), hlength (p n) (hpL n)⟩

end PoincareConjecture.M65Perturbation
