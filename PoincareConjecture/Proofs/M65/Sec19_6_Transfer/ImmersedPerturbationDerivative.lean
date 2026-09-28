import PoincareConjecture.Proofs.M65.Sec19_6_Transfer.ImmersedPerturbationComposition
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Claim19_28.RelabelingConnection
import PoincareConjecture.Proofs.M09.VelocityChainRules

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Bundle Metric
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M65Perturbation

variable {M : Type u} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
  {n : ℕ}

theorem foldControls_parameter_smooth
    (Phi : Fin n → M × ℝ → M) (beta : Fin n → ℝ → ℝ) (d : ℝ) (hd : 0 < d)
    (hPhi : ∀ i, ContMDiffOn ((𝓡 3).prod (𝓘(ℝ, ℝ))) (𝓡 3) ∞ (Phi i)
      (univ ×ˢ Ioo (-d) d))
    (hbeta : ∀ i, ContDiff ℝ ∞ (beta i))
    (hbound : ∀ i x, |beta i x| ≤ 1) (L : List (Fin n)) (x : ℝ) (y : M) :
    ContMDiffAt 𝓘(ℝ, Fin n → ℝ) (𝓡 3) ∞
      (fun p => foldControls Phi beta L p x y) 0 := by
  have h : ContMDiffAt
      ((𝓘(ℝ, Fin n → ℝ)).prod ((𝓘(ℝ, ℝ)).prod (𝓡 3))) (𝓡 3) ∞
      (fun z : (Fin n → ℝ) × (ℝ × M) => foldControls Phi beta L z.1 z.2.1 z.2.2)
      (0, x, y) :=
    (foldControls_contMDiffOn Phi beta d hPhi hbeta hbound L).contMDiffAt
      ((isOpen_ball.prod isOpen_univ).mem_nhds ⟨mem_ball_self hd, mem_univ (x, y)⟩)
  exact h.comp 0 (contMDiff_id.prodMk contMDiff_const).contMDiffAt

theorem foldControls_single_velocity
    (Phi : Fin n → M × ℝ → M) (beta : Fin n → ℝ → ℝ) (d : ℝ) (hd : 0 < d)
    (hPhi : ∀ i, ContMDiffOn ((𝓡 3).prod (𝓘(ℝ, ℝ))) (𝓡 3) ∞ (Phi i)
      (univ ×ˢ Ioo (-d) d))
    (hzero : ∀ i y, Phi i (y, 0) = y)
    (L : List (Fin n)) (hL : L.Nodup) (j : Fin n) (hj : j ∈ L)
    (x : ℝ) (y : M) :
    curveVelocity (n := 3) (fun r => foldControls Phi beta L (Pi.single j r) x y) 0 =
      beta j x • curveVelocity (n := 3) (fun r => Phi j (y, r)) 0 := by
  have hline : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 3) (fun r => Phi j (y, r)) 0 := by
    have h : ContMDiffAt ((𝓡 3).prod (𝓘(ℝ, ℝ))) (𝓡 3) ∞ (Phi j) (y, 0) :=
      (hPhi j).contMDiffAt
        ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ y, neg_neg_of_pos hd, hd⟩)
    exact (h.comp 0 (contMDiff_const.prodMk contMDiff_id).contMDiffAt).mdifferentiableAt
      (by simp)
  have hweight : HasDerivAt (fun r : ℝ => beta j x * r) (beta j x) 0 := by
    simpa only [mul_one, id_eq] using (hasDerivAt_id (0 : ℝ)).const_mul (beta j x)
  have hchain := m65CurveVelocity_comp
    (by simpa only [mul_zero] using hline) hweight
  have hfun : (fun r => foldControls Phi beta L (Pi.single j r) x y) =
      (fun r => Phi j (y, r)) ∘ (fun r => beta j x * r) := by
    funext r
    exact foldControls_single Phi beta hzero L hL j hj r x y
  rw [hfun]
  have hv : (curveVelocity (n := 3) (fun r => Phi j (y, r)) (beta j x * 0) : LoopAmbient) =
      curveVelocity (n := 3) (fun r => Phi j (y, r)) 0 :=
    congrArg (fun t => (curveVelocity (n := 3) (fun r => Phi j (y, r)) t : LoopAmbient))
      (mul_zero (beta j x))
  exact hchain.trans (congrArg (fun v : LoopAmbient => beta j x • v) hv)

variable [IsManifold (𝓡 3) ∞ M]

theorem foldControls_mfderiv_single
    (Phi : Fin n → M × ℝ → M) (beta : Fin n → ℝ → ℝ) (d : ℝ) (hd : 0 < d)
    (hPhi : ∀ i, ContMDiffOn ((𝓡 3).prod (𝓘(ℝ, ℝ))) (𝓡 3) ∞ (Phi i)
      (univ ×ˢ Ioo (-d) d))
    (hzero : ∀ i y, Phi i (y, 0) = y)
    (hbeta : ∀ i, ContDiff ℝ ∞ (beta i))
    (hbound : ∀ i x, |beta i x| ≤ 1)
    (L : List (Fin n)) (hL : L.Nodup) (j : Fin n) (hj : j ∈ L)
    (x : ℝ) (y : M) :
    mfderiv 𝓘(ℝ, Fin n → ℝ) (𝓡 3)
      (fun p => foldControls Phi beta L p x y) 0 (Pi.single j 1) =
      beta j x • curveVelocity (n := 3) (fun r => Phi j (y, r)) 0 := by
  have hf := (foldControls_parameter_smooth Phi beta d hd hPhi hbeta hbound L x y).mdifferentiableAt
    (by simp)
  have hline := Proofs.M09.curveVelocity_comp_initial_line
    (fun p => foldControls Phi beta L p x y) 0 (Pi.single j 1) hf
  have hsingle : (fun r : ℝ => (0 : Fin n → ℝ) + r • Pi.single j 1) =
      (fun r => (Pi.single j r : Fin n → ℝ)) := by
    funext r i
    by_cases hij : i = j <;> simp [hij]
  rw [show (fun r => foldControls Phi beta L (0 + r • Pi.single j 1) x y) =
      (fun r => foldControls Phi beta L (Pi.single j r) x y) from
        congrArg (fun line : ℝ → (Fin n → ℝ) =>
          fun r => foldControls Phi beta L (line r) x y) hsingle] at hline
  exact hline.symm.trans (foldControls_single_velocity Phi beta d hd hPhi hzero L hL j hj x y)

theorem foldControls_chart_fderiv_single
    (Phi : Fin n → M × ℝ → M) (beta : Fin n → ℝ → ℝ) (d : ℝ) (hd : 0 < d)
    (hPhi : ∀ i, ContMDiffOn ((𝓡 3).prod (𝓘(ℝ, ℝ))) (𝓡 3) ∞ (Phi i)
      (univ ×ˢ Ioo (-d) d))
    (hzero : ∀ i y, Phi i (y, 0) = y)
    (hbeta : ∀ i, ContDiff ℝ ∞ (beta i))
    (hbound : ∀ i x, |beta i x| ≤ 1)
    (L : List (Fin n)) (hL : L.Nodup) (j : Fin n) (hj : j ∈ L)
    (x : ℝ) (y q : M) (hy : y ∈ (chartAt LoopAmbient q).source) :
    fderiv ℝ (fun p => (chartAt LoopAmbient q) (foldControls Phi beta L p x y)) 0
      (Pi.single j 1) =
      beta j x • mfderiv (𝓡 3) (𝓡 3) (chartAt LoopAmbient q) y
        (curveVelocity (n := 3) (fun r => Phi j (y, r)) 0) := by
  have hf := (foldControls_parameter_smooth Phi beta d hd hPhi hbeta hbound L x y).mdifferentiableAt
    (by simp)
  have hpoint : foldControls Phi beta L 0 x y = y :=
    foldControls_eq_of_zero Phi beta hzero L 0 x y (fun _ _ => rfl)
  have he : MDifferentiableAt (𝓡 3) (𝓡 3) (chartAt LoopAmbient q)
      (foldControls Phi beta L 0 x y) := by
    rw [hpoint]
    exact mdifferentiableAt_atlas (chart_mem_atlas LoopAmbient q) hy
  have hchain := mfderiv_comp_apply (f := fun p => foldControls Phi beta L p x y)
    (g := chartAt LoopAmbient q) 0 he hf (Pi.single j 1)
  have hcolumn := foldControls_mfderiv_single Phi beta d hd hPhi hzero hbeta hbound
    L hL j hj x y
  have hchart := mfderiv_congr_point (I := 𝓡 3) (I' := 𝓡 3)
    (f := chartAt LoopAmbient q) hpoint
  simpa +instances only [mfderiv_eq_fderiv, Function.comp_def, hcolumn, hchart, map_smul]
    using! hchain

end PoincareConjecture.M65Perturbation
