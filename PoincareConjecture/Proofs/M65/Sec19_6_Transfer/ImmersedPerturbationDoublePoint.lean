import PoincareConjecture.Proofs.M65.Sec19_6_Transfer.ImmersedPerturbationBlock
import PoincareConjecture.Proofs.M65.Sec19_6_Transfer.ImmersedPerturbationFamily

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Metric
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M65Perturbation

variable {M : Type u} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
  [IsManifold (𝓡 3) ∞ M] {a b : ℝ} {F : RicciFlow 3 M (Icc a b)}
  {J : Set ℝ} {n : ℕ}

def doublePointEquation (C : M65SmoothFilledLoopFamily F J)
    (Phi : Fin n → M × ℝ → M) (beta : Fin n → ℝ → ℝ) (L : List (Fin n)) (q : M)
    (w : (Fin n → ℝ) × LoopAmbient) : LoopAmbient :=
  (chartAt LoopAmbient q) (foldControls Phi beta L w.1 (w.2 0)
    (periodicFreeLoop (C.loops (w.2 2)) (w.2 0))) -
  (chartAt LoopAmbient q) (foldControls Phi beta L w.1 (w.2 1)
    (periodicFreeLoop (C.loops (w.2 2)) (w.2 1)))

theorem doublePointEquation_contDiffAt (C : M65SmoothFilledLoopFamily F J) (hJ : IsOpen J)
    (Phi : Fin n → M × ℝ → M) (beta : Fin n → ℝ → ℝ) (d : ℝ) (hd : 0 < d)
    (hPhi : ∀ i, ContMDiffOn ((𝓡 3).prod (𝓘(ℝ, ℝ))) (𝓡 3) ∞ (Phi i)
      (univ ×ˢ Ioo (-d) d))
    (hzero : ∀ i y, Phi i (y, 0) = y)
    (hbeta : ∀ i, ContDiff ℝ ∞ (beta i)) (hbound : ∀ i x, |beta i x| ≤ 1)
    (L : List (Fin n)) (q : M) (z : LoopAmbient) (ht : z 2 ∈ J)
    (hx : periodicFreeLoop (C.loops (z 2)) (z 0) ∈ (chartAt LoopAmbient q).source)
    (hy : periodicFreeLoop (C.loops (z 2)) (z 1) ∈ (chartAt LoopAmbient q).source) :
    ContDiffAt ℝ ∞ (doublePointEquation C Phi beta L q) (0, z) := by
  have hfamily := foldControls_family_smooth F C Phi beta d hPhi hbeta hbound L
  have hpart (i : Fin 3)
      (hi : periodicFreeLoop (C.loops (z 2)) (z i) ∈ (chartAt LoopAmbient q).source) :
      ContDiffAt ℝ ∞ (fun w : (Fin n → ℝ) × LoopAmbient =>
        (chartAt LoopAmbient q) (foldControls Phi beta L w.1 (w.2 i)
          (periodicFreeLoop (C.loops (w.2 2)) (w.2 i)))) (0, z) := by
    have hselect : ContDiff ℝ ∞ (fun w : (Fin n → ℝ) × LoopAmbient =>
        (w.1, (w.2 i, w.2 2))) :=
      contDiff_fst.prodMk (((EuclideanSpace.proj i : LoopAmbient →L[ℝ] ℝ).contDiff.comp
        contDiff_snd).prodMk ((EuclideanSpace.proj 2 : LoopAmbient →L[ℝ] ℝ).contDiff.comp
          contDiff_snd))
    have hfold := (hfamily.contMDiffAt
      ((isOpen_ball.prod (isOpen_univ.prod hJ)).mem_nhds
        ⟨mem_ball_self hd, mem_univ (z i), ht⟩)).comp (0, z) hselect.contMDiff.contMDiffAt
    have hpoint : foldControls Phi beta L 0 (z i)
        (periodicFreeLoop (C.loops (z 2)) (z i)) =
        periodicFreeLoop (C.loops (z 2)) (z i) :=
      foldControls_eq_of_zero Phi beta hzero L 0 _ _ (fun _ _ => rfl)
    have he : ContMDiffAt (𝓡 3) (𝓡 3) ∞ (chartAt LoopAmbient q)
        (foldControls Phi beta L 0 (z i) (periodicFreeLoop (C.loops (z 2)) (z i))) := by
      rw [hpoint]
      exact contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas q) hi
    exact (he.comp (0, z) hfold).contDiffAt
  exact (hpart 0 hx).sub (hpart 1 hy)

theorem doublePointEquation_fderiv_single (C : M65SmoothFilledLoopFamily F J)
    (Phi : Fin n → M × ℝ → M) (beta : Fin n → ℝ → ℝ) (d : ℝ) (hd : 0 < d)
    (hPhi : ∀ i, ContMDiffOn ((𝓡 3).prod (𝓘(ℝ, ℝ))) (𝓡 3) ∞ (Phi i)
      (univ ×ˢ Ioo (-d) d))
    (hzero : ∀ i y, Phi i (y, 0) = y)
    (hbeta : ∀ i, ContDiff ℝ ∞ (beta i)) (hbound : ∀ i x, |beta i x| ≤ 1)
    (L : List (Fin n)) (hL : L.Nodup) (j : Fin n) (hj : j ∈ L)
    (q : M) (z : LoopAmbient)
    (hx : periodicFreeLoop (C.loops (z 2)) (z 0) ∈ (chartAt LoopAmbient q).source)
    (hy : periodicFreeLoop (C.loops (z 2)) (z 1) ∈ (chartAt LoopAmbient q).source) :
    fderiv ℝ (fun p => doublePointEquation C Phi beta L q (p, z)) 0 (Pi.single j 1) =
      (@HSMul.hSMul ℝ LoopAmbient LoopAmbient _ (beta j (z 0))
        (mfderiv (𝓡 3) (𝓡 3) (chartAt LoopAmbient q)
        (periodicFreeLoop (C.loops (z 2)) (z 0))
        (curveVelocity (n := 3) (fun r => Phi j (periodicFreeLoop (C.loops (z 2)) (z 0), r)) 0) :
          LoopAmbient)) -
      (@HSMul.hSMul ℝ LoopAmbient LoopAmbient _ (beta j (z 1))
        (mfderiv (𝓡 3) (𝓡 3) (chartAt LoopAmbient q)
        (periodicFreeLoop (C.loops (z 2)) (z 1))
        (curveVelocity (n := 3) (fun r => Phi j (periodicFreeLoop (C.loops (z 2)) (z 1), r)) 0) :
          LoopAmbient)) := by
  have hpart (i : Fin 3)
      (hi : periodicFreeLoop (C.loops (z 2)) (z i) ∈ (chartAt LoopAmbient q).source) :
      DifferentiableAt ℝ (fun p => (chartAt LoopAmbient q)
        (foldControls Phi beta L p (z i) (periodicFreeLoop (C.loops (z 2)) (z i)))) 0 := by
    have hf := foldControls_parameter_smooth Phi beta d hd hPhi hbeta hbound L (z i)
      (periodicFreeLoop (C.loops (z 2)) (z i))
    have hpoint := foldControls_eq_of_zero Phi beta hzero L 0 (z i)
      (periodicFreeLoop (C.loops (z 2)) (z i)) (fun _ _ => rfl)
    have he : ContMDiffAt (𝓡 3) (𝓡 3) ∞ (chartAt LoopAmbient q)
        (foldControls Phi beta L 0 (z i) (periodicFreeLoop (C.loops (z 2)) (z i))) := by
      rw [hpoint]
      exact contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas q) hi
    exact (he.comp 0 hf).contDiffAt.differentiableAt (by simp)
  have hsub := congrArg (fun A : (Fin n → ℝ) →L[ℝ] LoopAmbient => A (Pi.single j 1))
    (((hpart 0 hx).hasFDerivAt.sub (hpart 1 hy).hasFDerivAt).fderiv)
  have hcolumns := congrArg₂ (fun v w : LoopAmbient => v - w)
    (foldControls_chart_fderiv_single Phi beta d hd hPhi hzero hbeta hbound L hL j hj
      (z 0) _ q hx)
    (foldControls_chart_fderiv_single Phi beta d hd hPhi hzero hbeta hbound L hL j hj
      (z 1) _ q hy)
  exact hsub.trans hcolumns

variable [T2Space M] [CompactSpace M]

set_option maxHeartbeats 700000 in

theorem exists_doublePoint_regular_controls (C : M65SmoothFilledLoopFamily F J)
    (z : LoopAmbient)
    (hxy : (⟨Proofs.M58.angularPoint (z 0), Proofs.M58.norm_angularPoint (z 0)⟩ : LoopCircle) ≠
      ⟨Proofs.M58.angularPoint (z 1), Proofs.M58.norm_angularPoint (z 1)⟩)
    (heq : periodicFreeLoop (C.loops (z 2)) (z 0) = periodicFreeLoop (C.loops (z 2)) (z 1)) :
    ∃ (d : ℝ) (beta : LoopPlane → ℝ) (Phi : Fin 3 → M × ℝ → M),
      0 < d ∧ ContDiff ℝ ∞ beta ∧ (∀ w, beta w ∈ Icc (0 : ℝ) 1) ∧
      beta (Proofs.M58.angularPoint (z 0)) = 1 ∧
      beta (Proofs.M58.angularPoint (z 1)) = 0 ∧
      (∀ i, ContMDiffOn ((𝓡 3).prod (𝓘(ℝ, ℝ))) (𝓡 3) ∞ (Phi i)
        (univ ×ˢ Ioo (-d) d)) ∧
      (∀ i y, Phi i (y, 0) = y) ∧
      Function.Bijective (fderiv ℝ (fun p =>
        doublePointEquation C Phi (fun _ x => beta (Proofs.M58.angularPoint x))
          (List.finRange 3) (periodicFreeLoop (C.loops (z 2)) (z 0)) (p, z)) 0) := by
  let q := periodicFreeLoop (C.loops (z 2)) (z 0)
  obtain ⟨d, beta, Phi, hd, hbeta, hbound, hx, hy, hPhi, hzero, hvel⟩ :=
    exists_double_point_controls
      ⟨Proofs.M58.angularPoint (z 0), Proofs.M58.norm_angularPoint (z 0)⟩
      ⟨Proofs.M58.angularPoint (z 1), Proofs.M58.norm_angularPoint (z 1)⟩ hxy q
  obtain ⟨hweight, _, hweightBound⟩ := source_weight_regular beta hbeta hbound
  let A := fderiv ℝ (fun p => doublePointEquation C Phi
    (fun _ x => beta (Proofs.M58.angularPoint x)) (List.finRange 3) q (p, z)) 0
  have hcol (i : Fin 3) : A (Pi.single i 1) = EuclideanSpace.single i 1 := by
    have hxq : periodicFreeLoop (C.loops (z 2)) (z 0) ∈ (chartAt LoopAmbient q).source :=
      mem_chart_source _ _
    have hyq : periodicFreeLoop (C.loops (z 2)) (z 1) ∈ (chartAt LoopAmbient q).source :=
      heq ▸ hxq
    have hcolumn := doublePointEquation_fderiv_single C Phi
      (fun _ x => beta (Proofs.M58.angularPoint x)) d hd hPhi hzero
      (fun _ => hweight) (fun _ => hweightBound) (List.finRange 3)
      (List.nodup_finRange 3) i (List.mem_finRange i) q z hxq hyq
    have hfirst : A (Pi.single i 1) =
        mfderiv (𝓡 3) (𝓡 3) (chartAt LoopAmbient q) q
          (curveVelocity (n := 3) (fun r => Phi i (q, r)) 0) := by
      simpa +instances only [hx, hy, one_smul, zero_smul, sub_zero] using! hcolumn
    exact hfirst.trans (hvel i)
  let B := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm
  have hAB : A = B.toContinuousLinearMap := by
    apply ContinuousLinearMap.coe_injective
    apply LinearMap.pi_ext
    intro i r
    have hr : (Pi.single i r : Fin 3 → ℝ) = r • Pi.single i 1 := by
      ext j
      by_cases hji : j = i <;> simp [hji]
    change A (Pi.single i r) = B (Pi.single i r)
    rw [hr, map_smul, map_smul, hcol]
    rfl
  refine ⟨d, beta, Phi, hd, hbeta, hbound, hx, hy, hPhi, hzero, ?_⟩
  change Function.Bijective A
  rw [hAB]
  exact B.bijective

end PoincareConjecture.M65Perturbation
