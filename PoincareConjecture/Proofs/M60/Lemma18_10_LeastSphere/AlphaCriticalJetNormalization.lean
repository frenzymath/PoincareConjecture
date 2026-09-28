import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AlphaCriticalJetCoefficients









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Metric
open scoped ContDiff Topology ENNReal Manifold

noncomputable section

namespace PoincareConjecture.M60

private abbrev E (m : ℕ) := EuclideanSpace ℝ (Fin m)
private abbrev Grad (m : ℕ) := E m × E m
private abbrev Point (m : ℕ) := (LoopPlane × E m) × Grad m

local instance jetNormalizationBilinearNormedGroup {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    NormedAddCommGroup (F →L[ℝ] F →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup

local instance jetNormalizationBilinearNormedSpace {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    NormedSpace ℝ (F →L[ℝ] F →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

local instance jetNormalizationMixedNormedGroup {m : ℕ} :
    NormedAddCommGroup (Grad m →L[ℝ] E m →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup

local instance jetNormalizationMixedNormedSpace {m : ℕ} :
    NormedSpace ℝ (Grad m →L[ℝ] E m →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace


def suJetBlockDiagonal {k m : ℕ} (A : E m →L[ℝ] E m) : E (k * m) →L[ℝ] E (k * m) :=
  LinearMap.toContinuousLinearMap {
    toFun := fun v => WithLp.toLp 2 fun a =>
      let j := (finProdFinEquiv : Fin k × Fin m ≃ Fin (k * m)).symm a
      A (suJetBlock j.1 v) j.2
    map_add' := by intro v w; ext a; simp
    map_smul' := by intro c v; ext a; simp
  }

theorem suJetBlock_diagonal {k m : ℕ} (A : E m →L[ℝ] E m) (j : Fin k) (v : E (k * m)) :
    suJetBlock j (suJetBlockDiagonal A v) = A (suJetBlock j v) := by
  ext a
  change A (suJetBlock ((finProdFinEquiv : Fin k × Fin m ≃ Fin (k * m)).symm
    (finProdFinEquiv (j, a))).1 v) ((finProdFinEquiv : Fin k × Fin m ≃ Fin (k * m)).symm
      (finProdFinEquiv (j, a))).2 = A (suJetBlock j v) a
  simp only [Equiv.symm_apply_apply]

theorem suJetBlock_ext {k m : ℕ} {v w : E (k * m)}
    (h : ∀ j : Fin k, suJetBlock j v = suJetBlock j w) : v = w := by
  ext a
  obtain ⟨⟨j, a⟩, rfl⟩ := (finProdFinEquiv : Fin k × Fin m ≃ Fin (k * m)).surjective a
  exact congrArg (fun v : E m => v a) (h j)



def suJetBlockDiagonalL {k m : ℕ} : (E m →L[ℝ] E m) →L[ℝ] E (k * m) →L[ℝ] E (k * m) :=
  LinearMap.toContinuousLinearMap {
    toFun := suJetBlockDiagonal
    map_add' := by
      intro A B
      apply ContinuousLinearMap.ext
      intro v
      apply suJetBlock_ext
      intro j
      simp only [add_apply, map_add, suJetBlock_diagonal]
    map_smul' := by
      intro c A
      apply ContinuousLinearMap.ext
      intro v
      apply suJetBlock_ext
      intro j
      simp only [smul_apply, map_smul, suJetBlock_diagonal, RingHom.id_apply]
  }



def suJetBlockDiagonalEquiv {k m : ℕ} (L : E m ≃L[ℝ] E m) : E (k * m) ≃L[ℝ] E (k * m) where
  toLinearEquiv := {
    toLinearMap := (suJetBlockDiagonal L.toContinuousLinearMap).toLinearMap
    invFun := suJetBlockDiagonal L.symm.toContinuousLinearMap
    left_inv := by
      intro v
      apply suJetBlock_ext
      intro j
      change suJetBlock j (suJetBlockDiagonal L.symm.toContinuousLinearMap
        (suJetBlockDiagonal L.toContinuousLinearMap v)) = suJetBlock j v
      simp only [suJetBlock_diagonal, ContinuousLinearEquiv.coe_coe, L.symm_apply_apply]
    right_inv := by
      intro v
      apply suJetBlock_ext
      intro j
      change suJetBlock j (suJetBlockDiagonal L.toContinuousLinearMap
        (suJetBlockDiagonal L.symm.toContinuousLinearMap v)) = suJetBlock j v
      simp only [suJetBlock_diagonal, ContinuousLinearEquiv.coe_coe, L.apply_symm_apply]
  }
  continuous_toFun := (suJetBlockDiagonal L.toContinuousLinearMap).continuous
  continuous_invFun := (suJetBlockDiagonal L.symm.toContinuousLinearMap).continuous

theorem suJetBlock_diagonalEquiv {k m : ℕ} (L : E m ≃L[ℝ] E m)
    (j : Fin k) (v : E (k * m)) :
    suJetBlock j (suJetBlockDiagonalEquiv L v) = L (suJetBlock j v) :=
  suJetBlock_diagonal L.toContinuousLinearMap j v



theorem suJetBlock_principalTrace {m : ℕ} (C : SUAffineJetCoefficients m)
    (z : LoopPlane × E (3 * m)) (H : Fin 2 → Fin 2 → E (3 * m)) (j : Fin 3) :
    suJetBlock j (C.prolong.principalTrace z H) =
      C.principalTrace (z.1, suJetBlock (0 : Fin 3) z.2)
        (fun i k => suJetBlock j (H i k)) := by
  classical
  ext a
  change C.prolong.principalTrace z H (finProdFinEquiv (j, a)) = _
  simp only [SUAffineJetCoefficients.principalTrace, SUAffineJetCoefficients.prolong,
    suJetBlockPrincipal, sum_apply, ContinuousLinearMap.bilinearComp_apply,
    suJetBlock_columnBasis]
  simp only [apply_ite, map_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rfl




def SUAffineJetNormalization.prolong {m : ℕ} {C : SUAffineJetCoefficients m}
    {O : Set (LoopPlane × E m)} {delta : ℝ}
    (N : SUAffineJetNormalization C O delta) (hdelta : 0 ≤ delta) :
    SUAffineJetNormalization C.prolong
      {z | (z.1, suJetBlock (0 : Fin 3) z.2) ∈ O} delta where
  targetChange := suJetBlockDiagonalEquiv N.targetChange
  normalizer z := suJetBlockDiagonal (N.normalizer (z.1, suJetBlock (0 : Fin 3) z.2))
  normalizer_smooth := by
    have hp : ContDiff ℝ ∞ (fun z : LoopPlane × E (3 * m) =>
        (z.1, suJetBlock (0 : Fin 3) z.2)) := by fun_prop
    exact suJetBlockDiagonalL.contDiff.comp_contDiffOn
      (N.normalizer_smooth.comp hp.contDiffOn (fun _ hz => hz))
  residual_bound := by
    intro z hz H
    let p := (z.1, suJetBlock (0 : Fin 3) z.2)
    let L := suJetBlockDiagonalEquiv (k := 3) N.targetChange
    let D := suJetBlockDiagonal (k := 3) (N.normalizer p)
    let R := (∑ i : Fin 2, H i i) - D (C.prolong.principalTrace z H)
    have hb (j : Fin 3) : suJetBlock j (L R) =
        N.targetChange ((∑ i : Fin 2, suJetBlock j (H i i)) -
          N.normalizer p (C.principalTrace p (fun i k => suJetBlock j (H i k)))) := by
      rw [suJetBlock_diagonalEquiv]
      dsimp only [R, D]
      rw [map_sub, map_sum, suJetBlock_diagonal, suJetBlock_principalTrace]
    have hs (j : Fin 3) : ‖suJetBlock j (L R)‖ ^ 2 ≤
        delta ^ 2 * ∑ i : Fin 2, ∑ k : Fin 2, ‖N.targetChange (suJetBlock j (H i k))‖ ^ 2 := by
      rw [hb]
      have h := pow_le_pow_left₀ (norm_nonneg _)
        (N.residual_bound p hz (fun i k => suJetBlock j (H i k))) 2
      rw [mul_pow, Real.sq_sqrt (Finset.sum_nonneg fun i _ =>
        Finset.sum_nonneg fun k _ => sq_nonneg _)] at h
      exact h
    have hblocks (i k : Fin 2) :
        (∑ j : Fin 3, ‖N.targetChange (suJetBlock j (H i k))‖ ^ 2) = ‖L (H i k)‖ ^ 2 := by
      simpa only [L, suJetBlock_diagonalEquiv] using suJetBlock_norm_sq (L (H i k))
    have hsum : ‖L R‖ ^ 2 ≤
        delta ^ 2 * ∑ i : Fin 2, ∑ k : Fin 2, ‖L (H i k)‖ ^ 2 := by
      have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hs j)
      rw [suJetBlock_norm_sq, ← Finset.mul_sum] at hh
      have he : (∑ j : Fin 3, ∑ i : Fin 2, ∑ k : Fin 2,
          ‖N.targetChange (suJetBlock j (H i k))‖ ^ 2) =
          ∑ i : Fin 2, ∑ k : Fin 2, ‖L (H i k)‖ ^ 2 := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
        simp only [hblocks]
      rwa [he] at hh
    have hsqrt := Real.sq_sqrt (show 0 ≤ ∑ i : Fin 2, ∑ k : Fin 2,
        ‖L (H i k)‖ ^ 2 from Finset.sum_nonneg fun i _ =>
          Finset.sum_nonneg fun k _ => sq_nonneg _)
    have hright : 0 ≤ delta * Real.sqrt (∑ i : Fin 2, ∑ k : Fin 2, ‖L (H i k)‖ ^ 2) :=
      mul_nonneg hdelta (Real.sqrt_nonneg _)
    change ‖L R‖ ≤ delta * Real.sqrt (∑ i : Fin 2, ∑ k : Fin 2, ‖L (H i k)‖ ^ 2)
    nlinarith [norm_nonneg (L R)]




theorem SUAffineJetCoefficients.prolong_smooth {m : ℕ} (C : SUAffineJetCoefficients m)
    {O : Set (LoopPlane × E m)} (hO : IsOpen O)
    (hA : ContDiffOn ℝ ∞ C.principal O) (hc : ContDiffOn ℝ ∞ C.fluxOffset O)
    (hB : ContDiffOn ℝ ∞ C.sourceLinear O) (hd : ContDiffOn ℝ ∞ C.sourceOffset O) :
    let P : Set (LoopPlane × E (3 * m)) := {z | (z.1, suJetBlock (0 : Fin 3) z.2) ∈ O}
    ContDiffOn ℝ ∞ C.prolong.principal P ∧ ContDiffOn ℝ ∞ C.prolong.fluxOffset P ∧
      ContDiffOn ℝ ∞ C.prolong.sourceLinear P ∧ ContDiffOn ℝ ∞ C.prolong.sourceOffset P := by
  classical
  let p (z : LoopPlane × E (3 * m)) := (z.1, suJetBlock (0 : Fin 3) z.2)
  let q (z : LoopPlane × E (3 * m)) := (suJetBlock (1 : Fin 3) z.2,
    suJetBlock (2 : Fin 3) z.2)
  have hp : ContDiff ℝ ∞ p := by fun_prop
  have hq : ContDiff ℝ ∞ q := by fun_prop
  have hall (z : LoopPlane × E (3 * m)) (hz : p z ∈ O) :
      ContDiffAt ℝ ∞ C.prolong.principal z ∧ ContDiffAt ℝ ∞ C.prolong.fluxOffset z ∧
        ContDiffAt ℝ ∞ C.prolong.sourceLinear z ∧ ContDiffAt ℝ ∞ C.prolong.sourceOffset z := by
    have hAz := hA.contDiffAt (hO.mem_nhds hz)
    have hcz := hc.contDiffAt (hO.mem_nhds hz)
    have hBz := hB.contDiffAt (hO.mem_nhds hz)
    have hdz := hd.contDiffAt (hO.mem_nhds hz)
    have hAc := hAz.comp z hp.contDiffAt
    have hcc := hcz.comp z hp.contDiffAt
    have hBc := hBz.comp z hp.contDiffAt
    have hdc := hdz.comp z hp.contDiffAt
    have hDA := (hAz.fderiv_right (m := ∞) (by simp)).comp z hp.contDiffAt
    have hDc := (hcz.fderiv_right (m := ∞) (by simp)).comp z hp.contDiffAt
    have hDB := (hBz.fderiv_right (m := ∞) (by simp)).comp z hp.contDiffAt
    have hDd := (hdz.fderiv_right (m := ∞) (by simp)).comp z hp.contDiffAt
    have hv (k : Fin 2) : ContDiffAt ℝ ∞
        (fun w : LoopPlane × E (3 * m) =>
          (EuclideanSpace.single k (1 : ℝ), suJetBlock k.succ w.2)) z :=
      contDiffAt_const.prodMk ((suJetBlock k.succ).contDiff.contDiffAt.comp z contDiffAt_snd)
    refine ⟨suJetBlockPrincipal_contDiff.contDiffAt.comp z hAc, ?_, ?_, ?_⟩
    · change ContDiffAt ℝ ∞ (fun w =>
        (C.fluxOffset (p w)).comp ((suJetBlock (0 : Fin 3)).prodMap (suJetBlock (0 : Fin 3))) +
          ∑ k : Fin 2, (fderiv ℝ C.principal (p w)
            (EuclideanSpace.single k 1, suJetBlock k.succ w.2) (q w) +
              fderiv ℝ C.fluxOffset (p w)
                (EuclideanSpace.single k 1, suJetBlock k.succ w.2)).comp
                  ((suJetBlock k.succ).prodMap (suJetBlock k.succ))) z
      apply ContDiffAt.add (hcc.clm_comp contDiffAt_const)
      apply ContDiffAt.sum
      intro k _
      exact (((hDA.clm_apply (hv k)).clm_apply hq.contDiffAt).add
        (hDc.clm_apply (hv k))).clm_comp contDiffAt_const
    · change ContDiffAt ℝ ∞ (fun w => ∑ j : Fin 3,
        ((ContinuousLinearMap.compL ℝ (E (3 * m)) (E m) ℝ).flip (suJetBlock j)).comp
          ((C.sourceLinear (p w)).comp ((suJetBlock j).prodMap (suJetBlock j)))) z
      apply ContDiffAt.sum
      intro j _
      exact contDiffAt_const.clm_comp (hBc.clm_comp contDiffAt_const)
    · change ContDiffAt ℝ ∞ (fun w => (C.sourceOffset (p w)).comp (suJetBlock (0 : Fin 3)) +
        ∑ k : Fin 2, (fderiv ℝ C.sourceLinear (p w)
          (EuclideanSpace.single k 1, suJetBlock k.succ w.2) (q w) +
            fderiv ℝ C.sourceOffset (p w)
              (EuclideanSpace.single k 1, suJetBlock k.succ w.2)).comp (suJetBlock k.succ)) z
      apply ContDiffAt.add (hdc.clm_comp contDiffAt_const)
      apply ContDiffAt.sum
      intro k _
      exact (((hDB.clm_apply (hv k)).clm_apply hq.contDiffAt).add
        (hDd.clm_apply (hv k))).clm_comp contDiffAt_const
  exact ⟨fun z hz => (hall z hz).1.contDiffWithinAt,
    fun z hz => (hall z hz).2.1.contDiffWithinAt,
    fun z hz => (hall z hz).2.2.1.contDiffWithinAt,
    fun z hz => (hall z hz).2.2.2.contDiffWithinAt⟩

end PoincareConjecture.M60
