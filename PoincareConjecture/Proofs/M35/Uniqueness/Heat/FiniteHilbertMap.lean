import PoincareConjecture.Proofs.M35.Uniqueness.Heat.DirichletCompactness









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] {m : ℕ}

def finiteHilbertSingle (i : Fin m) : H →L[ℝ] PiLp 2 (fun _ : Fin m => H) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.single ℝ (fun _ : Fin m => H) i)

def finiteHilbertMap (J : V →L[ℝ] H) :
    PiLp 2 (fun _ : Fin m => V) →L[ℝ] PiLp 2 (fun _ : Fin m => H) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => J.comp (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => V) i)))

@[simp] theorem finiteHilbertMap_apply (J : V →L[ℝ] H)
    (u : PiLp 2 (fun _ : Fin m => V)) (i : Fin m) : finiteHilbertMap J u i = J (u i) := rfl

theorem finiteHilbertMap_eq_sum (J : V →L[ℝ] H) :
    finiteHilbertMap (m := m) J = ∑ i, (finiteHilbertSingle i).comp
      (J.comp (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => V) i)) := by
  ext u i
  simp [finiteHilbertMap_apply, finiteHilbertSingle, ContinuousLinearMap.comp_apply]

theorem finiteHilbertMap_compact (J : V →L[ℝ] H) (hc : IsCompactOperator J) :
    IsCompactOperator (finiteHilbertMap (m := m) J) := by
  rw [finiteHilbertMap_eq_sum]
  change (∑ i, (finiteHilbertSingle i).comp
    (J.comp (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => V) i))) ∈
      compactOperator (RingHom.id ℝ) (PiLp 2 (fun _ : Fin m => V))
        (PiLp 2 (fun _ : Fin m => H))
  apply Submodule.sum_mem
  intro i _
  exact (hc.comp_clm (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => V) i)).clm_comp
    (finiteHilbertSingle i)

theorem finiteHilbertMap_injective (J : V →L[ℝ] H) (hi : Function.Injective J) :
    Function.Injective (finiteHilbertMap (m := m) J) := by
  intro u v h
  apply PiLp.ext
  intro i
  exact hi (congrArg (fun w : PiLp 2 (fun _ : Fin m => H) => w i) h)

theorem norm_finiteHilbertMap_le (J : V →L[ℝ] H) :
    ‖finiteHilbertMap (m := m) J‖ ≤ ‖J‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro u
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [PiLp.norm_sq_eq_of_L2, mul_pow, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  exact (pow_le_pow_left₀ (norm_nonneg _) (J.le_opNorm (u i)) 2).trans_eq (mul_pow _ _ 2)

theorem finiteHilbertMap_denseRange (J : V →L[ℝ] H) (hd : DenseRange J) :
    DenseRange (finiteHilbertMap (m := m) J) := by
  let eV := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => V)
  let eH := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => H)
  have hpi : DenseRange (Pi.map (fun _ : Fin m => J)) := DenseRange.piMap (fun _ => hd)
  have hc : Continuous (Pi.map (fun _ : Fin m => J)) :=
    continuous_pi (fun i => J.continuous.comp (continuous_apply i))
  have h1 := hpi.comp eV.surjective.denseRange hc
  have h2 := eH.symm.surjective.denseRange.comp h1 eH.symm.continuous
  exact h2

end PoincareConjecture.M35.Uniqueness.Heat
