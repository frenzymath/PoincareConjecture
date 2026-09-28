import PoincareConjecture.Proofs.M65.Sec19_6_Transfer.ImmersedPerturbationDoublePoint











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Metric
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M65Perturbation



def controlBlock {k : ℕ} (i : Fin k) : (Fin 3 → ℝ) →L[ℝ] (Fin (k * 3) → ℝ) :=
  ContinuousLinearMap.pi (fun j => if (finProdFinEquiv.symm j).1 = i then
    ContinuousLinearMap.proj (finProdFinEquiv.symm j).2 else 0)




theorem controlBlock_single {k : ℕ} (i : Fin k) (j : Fin 3) :
    controlBlock i (Pi.single j 1) = Pi.single (finProdFinEquiv (i, j)) 1 := by
  ext v
  obtain ⟨⟨a, b⟩, rfl⟩ := finProdFinEquiv.surjective v
  change (if (finProdFinEquiv.symm (finProdFinEquiv (a, b))).1 = i then
    ContinuousLinearMap.proj (finProdFinEquiv.symm (finProdFinEquiv (a, b))).2 else 0)
      (Pi.single j 1) = _
  rw [finProdFinEquiv.symm_apply_apply]
  by_cases hai : a = i
  · subst a
    simp [Pi.single_apply, finProdFinEquiv.injective.eq_iff]
  · simp [hai, finProdFinEquiv.injective.eq_iff]

private theorem common_control_time {k : ℕ} (d : Fin k → ℝ) (hd : ∀ i, 0 < d i) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ i, delta ≤ d i := by
  have hfinite (s : Finset (Fin k)) : ∃ delta : ℝ, 0 < delta ∧ ∀ i ∈ s, delta ≤ d i := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1, one_pos, fun i hi => (Finset.notMem_empty i hi).elim⟩
    | @insert i s hi ih =>
      obtain ⟨delta, hdelta, hle⟩ := ih
      refine ⟨min delta (d i), lt_min hdelta (hd i), ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hle j hj)
  obtain ⟨delta, hdelta, hle⟩ := hfinite Finset.univ
  exact ⟨delta, hdelta, fun i => hle i (Finset.mem_univ i)⟩

variable {M : Type u} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
  [IsManifold (𝓡 3) ∞ M] {a b : ℝ} {F : RicciFlow 3 M (Icc a b)}
  {J : Set ℝ} {k : ℕ}

set_option maxHeartbeats 800000 in





theorem combined_control_block_eq (C : M65SmoothFilledLoopFamily F J)
    (d : Fin k → ℝ) (hd : ∀ i, 0 < d i)
    (beta : Fin k → LoopPlane → ℝ) (hbeta : ∀ i, ContDiff ℝ ∞ (beta i))
    (hbound : ∀ i w, beta i w ∈ Icc (0 : ℝ) 1)
    (Phi : Fin k → Fin 3 → M × ℝ → M)
    (hPhi : ∀ i j, ContMDiffOn ((𝓡 3).prod (𝓘(ℝ, ℝ))) (𝓡 3) ∞ (Phi i j)
      (univ ×ˢ Ioo (-(d i)) (d i)))
    (hzero : ∀ i j y, Phi i j (y, 0) = y)
    (i : Fin k) (q : M) (z : LoopAmbient)
    (hx : periodicFreeLoop (C.loops (z 2)) (z 0) ∈ (chartAt LoopAmbient q).source)
    (hy : periodicFreeLoop (C.loops (z 2)) (z 1) ∈ (chartAt LoopAmbient q).source) :
    (fderiv ℝ (fun p => doublePointEquation C
      (fun j => Phi (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2)
      (fun j x => beta (finProdFinEquiv.symm j).1 (Proofs.M58.angularPoint x))
      (List.finRange (k * 3)) q (p, z)) 0).comp (controlBlock i) =
        fderiv ℝ (fun p => doublePointEquation C (Phi i)
          (fun _ x => beta i (Proofs.M58.angularPoint x)) (List.finRange 3) q (p, z)) 0 := by
  obtain ⟨delta, hdelta, hle⟩ := common_control_time d hd
  let allPhi : Fin (k * 3) → M × ℝ → M :=
    fun j => Phi (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2
  let allBeta : Fin (k * 3) → ℝ → ℝ :=
    fun j x => beta (finProdFinEquiv.symm j).1 (Proofs.M58.angularPoint x)
  have hAllPhi (j : Fin (k * 3)) : ContMDiffOn ((𝓡 3).prod (𝓘(ℝ, ℝ))) (𝓡 3) ∞
      (allPhi j) (univ ×ˢ Ioo (-delta) delta) :=
    (hPhi (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2).mono
      (prod_mono Subset.rfl (Ioo_subset_Ioo (neg_le_neg (hle _)) (hle _)))
  have hweight (j : Fin k) := source_weight_regular (beta j) (hbeta j) (hbound j)
  let A := (fderiv ℝ (fun p => doublePointEquation C allPhi allBeta
    (List.finRange (k * 3)) q (p, z)) 0).comp (controlBlock i)
  let B := fderiv ℝ (fun p => doublePointEquation C (Phi i)
    (fun _ x => beta i (Proofs.M58.angularPoint x)) (List.finRange 3) q (p, z)) 0
  have hcol (j : Fin 3) : A (Pi.single j 1) = B (Pi.single j 1) := by
    have hglobal := doublePointEquation_fderiv_single C allPhi allBeta delta hdelta hAllPhi
      (fun v => hzero (finProdFinEquiv.symm v).1 (finProdFinEquiv.symm v).2)
      (fun v => (hweight (finProdFinEquiv.symm v).1).1)
      (fun v => (hweight (finProdFinEquiv.symm v).1).2.2)
      (List.finRange (k * 3)) (List.nodup_finRange _) (finProdFinEquiv (i, j))
      (List.mem_finRange _) q z hx hy
    have hPhiij : allPhi (finProdFinEquiv (i, j)) = Phi i j := by
      simp only [allPhi, finProdFinEquiv.symm_apply_apply]
    rw [hPhiij] at hglobal
    have hlocal := doublePointEquation_fderiv_single C (Phi i)
      (fun _ x => beta i (Proofs.M58.angularPoint x)) (d i) (hd i) (hPhi i) (hzero i)
      (fun _ => (hweight i).1) (fun _ => (hweight i).2.2)
      (List.finRange 3) (List.nodup_finRange _) j (List.mem_finRange _) q z hx hy
    change A (Pi.single j 1) = fderiv ℝ (fun p => doublePointEquation C (Phi i)
      (fun _ x => beta i (Proofs.M58.angularPoint x)) (List.finRange 3) q (p, z)) 0
        (Pi.single j 1)
    rw [hlocal]
    simpa +instances only [A, ContinuousLinearMap.comp_apply, controlBlock_single,
      allPhi, allBeta, finProdFinEquiv.symm_apply_apply] using! hglobal
  change A = B
  apply ContinuousLinearMap.coe_injective
  apply LinearMap.pi_ext
  intro j r
  have hr : (Pi.single j r : Fin 3 → ℝ) = r • Pi.single j 1 := by
    ext v
    by_cases hv : v = j <;> simp [hv]
  change A (Pi.single j r) = B (Pi.single j r)
  rw [hr, map_smul, map_smul, hcol]





theorem exists_combined_control_family (C : M65SmoothFilledLoopFamily F J)
    (d : Fin k → ℝ) (hd : ∀ i, 0 < d i)
    (beta : Fin k → LoopPlane → ℝ) (hbeta : ∀ i, ContDiff ℝ ∞ (beta i))
    (hbound : ∀ i w, beta i w ∈ Icc (0 : ℝ) 1)
    (Phi : Fin k → Fin 3 → M × ℝ → M)
    (hPhi : ∀ i j, ContMDiffOn ((𝓡 3).prod (𝓘(ℝ, ℝ))) (𝓡 3) ∞ (Phi i j)
      (univ ×ˢ Ioo (-(d i)) (d i)))
    (hzero : ∀ i j y, Phi i j (y, 0) = y) :
    ∃ (delta : ℝ) (Gamma : (Fin (k * 3) → ℝ) → ℝ → C1FreeLoopSpace (M := M)),
      0 < delta ∧ (∀ i, delta ≤ d i) ∧
      (∀ p ∈ ball 0 delta, ∀ t ∈ J, ∀ x,
        periodicFreeLoop (Gamma p t) x = foldControls
          (fun j => Phi (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2)
          (fun j x => beta (finProdFinEquiv.symm j).1 (Proofs.M58.angularPoint x))
          (List.finRange (k * 3)) p x (periodicFreeLoop (C.loops t) x)) ∧
      ContMDiffOn 𝓘(ℝ, (Fin (k * 3) → ℝ) × (ℝ × ℝ)) (𝓡 3) ∞
        (fun w => periodicFreeLoop (Gamma w.1 w.2.2) w.2.1)
        (ball 0 delta ×ˢ (univ ×ˢ J)) ∧
      ∀ t ∈ J, ∀ x, periodicFreeLoop (Gamma 0 t) x = periodicFreeLoop (C.loops t) x := by
  obtain ⟨delta, hdelta, hle⟩ := common_control_time d hd
  have hweight (i : Fin k) := source_weight_regular (beta i) (hbeta i) (hbound i)
  obtain ⟨Gamma, hGamma, hsmooth, hbase⟩ := exists_controlled_loop_family F C
    (fun j : Fin (k * 3) => Phi (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2)
    (fun j x => beta (finProdFinEquiv.symm j).1 (Proofs.M58.angularPoint x)) delta hdelta
    (fun j => (hPhi (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2).mono
      (prod_mono Subset.rfl (Ioo_subset_Ioo (neg_le_neg (hle _)) (hle _))))
    (fun j => hzero (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2)
    (fun j => (hweight (finProdFinEquiv.symm j).1).1)
    (fun j => (hweight (finProdFinEquiv.symm j).1).2.1)
    (fun j => (hweight (finProdFinEquiv.symm j).1).2.2) (List.finRange (k * 3))
  exact ⟨delta, Gamma, hdelta, hle, hGamma, hsmooth, hbase⟩

end PoincareConjecture.M65Perturbation
