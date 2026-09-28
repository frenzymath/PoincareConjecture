import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.ConstantEnergy
open MeasureTheory Set
open scoped ContDiff Topology

noncomputable section

namespace Poincare.Analysis.Parabolic.WeakRegularity.Canonical

variable {n : ℕ}

local instance : (volume : Measure (Spacetime n)).IsAddHaarMeasure := by
  change ((volume : Measure (Euclid n)).prod (volume : Measure ℝ)).IsAddHaarMeasure
  infer_instance

private theorem integrable_spatialSecond_mul
    {v : Spacetime n → ℝ} (hv : ContDiff ℝ ∞ v)
    (hvc : HasCompactSupport v) (i j k l : Fin n) :
    Integrable (fun z => spatialSecond i j v z * spatialSecond k l v z) volume := by
  apply (contDiff_spatialSecond hv i j).continuous.mul
    (contDiff_spatialSecond hv k l).continuous |>.integrable_of_hasCompactSupport
  exact (hasCompactSupport_spatialSecond i j hvc).mul_right

private theorem integral_laplacian_sq_eq_hessian
    {v : Spacetime n → ℝ} (hv : ContDiff ℝ ∞ v)
    (hvc : HasCompactSupport v) :
    (∫ z, (∑ k, spatialSecond k k v z) ^ 2) =
      ∫ z, ∑ i, ∑ j, (spatialSecond i j v z) ^ 2 := by
  have hdiag (i j : Fin n) := integral_spatialSecond_mul_diag hv hvc i i j
  have hprod (i j : Fin n) :
      Integrable (fun z => spatialSecond i i v z * spatialSecond j j v z) volume :=
    integrable_spatialSecond_mul hv hvc i i j j
  have hsq :
      Integrable (fun z => (∑ k, spatialSecond k k v z) ^ 2) volume := by
    have hdouble : (fun z => (∑ k, spatialSecond k k v z) ^ 2) =
        (fun z => ∑ k, ∑ l, spatialSecond k k v z * spatialSecond l l v z) := by
      funext z
      rw [pow_two, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
    rw [hdouble]
    apply integrable_finsetSum
    intro k hk
    apply integrable_finsetSum
    intro l hl
    exact hprod k l
  have hdouble : (fun z => (∑ k, spatialSecond k k v z) ^ 2) =
      (fun z => ∑ k, ∑ l, spatialSecond k k v z * spatialSecond l l v z) := by
    funext z
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
  have hsum_integral (k : Fin n) :
      (∫ z, ∑ l, spatialSecond k k v z * spatialSecond l l v z) =
        ∑ l, ∫ z, spatialSecond k k v z * spatialSecond l l v z := by
    rw [integral_finsetSum Finset.univ]
    intro l hl
    exact hprod k l
  have hsum_sq (i : Fin n) :
      (∫ z, ∑ j, (spatialSecond i j v z) ^ 2) =
        ∑ j, ∫ z, (spatialSecond i j v z) ^ 2 := by
    rw [integral_finsetSum Finset.univ]
    intro j hj
    exact integrable_spatialSecond_sq hv hvc i j
  have hintegrable_sq (i : Fin n) :
      Integrable (fun z => ∑ j, (spatialSecond i j v z) ^ 2) volume := by
    apply integrable_finsetSum
    intro j hj
    exact integrable_spatialSecond_sq hv hvc i j
  calc
    (∫ z, (∑ k, spatialSecond k k v z) ^ 2) =
        ∫ z, ∑ k, ∑ l, spatialSecond k k v z * spatialSecond l l v z := by
      rw [hdouble]
    _ = ∑ k, ∑ l, ∫ z, spatialSecond k k v z * spatialSecond l l v z := by
      rw [integral_finsetSum Finset.univ]
      · simp_rw [hsum_integral]
      · intro k hk
        apply integrable_finsetSum
        intro l hl
        exact hprod k l
    _ = ∑ k, ∑ l, ∫ z, spatialSecond k l v z * spatialSecond k l v z := by
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro l hl
      rw [hdiag k l]
    _ = ∫ z, ∑ i, ∑ j, (spatialSecond i j v z) ^ 2 := by
      rw [integral_finsetSum Finset.univ]
      · simp_rw [hsum_sq]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        simp only [pow_two]
      · intro i hi
        exact hintegrable_sq i

private theorem hasCompactSupport_laplacian
    {v : Spacetime n → ℝ} (hvc : HasCompactSupport v) :
    HasCompactSupport (fun z => ∑ k, spatialSecond k k v z) := by
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty => exact HasCompactSupport.zero
  | @insert k s hks ih =>
      simp only [Finset.sum_insert hks]
      exact (hasCompactSupport_spatialSecond k k hvc).add ih

private theorem contDiff_laplacian
    {v : Spacetime n → ℝ} (hv : ContDiff ℝ ∞ v) :
    ContDiff ℝ ∞ (fun z => ∑ k, spatialSecond k k v z) :=
  ContDiff.sum (fun k _ => contDiff_spatialSecond hv k k)

private theorem integrable_laplacian_sq
    {v : Spacetime n → ℝ} (hv : ContDiff ℝ ∞ v)
    (hvc : HasCompactSupport v) :
    Integrable (fun z => (∑ k, spatialSecond k k v z) ^ 2) volume := by
  have h := (contDiff_laplacian hv).continuous.mul (contDiff_laplacian hv).continuous
  have hi := h.integrable_of_hasCompactSupport (μ := (volume : Measure (Spacetime n)))
    (hasCompactSupport_laplacian hvc).mul_left
  convert hi using 1
  ext z
  simp only [pow_two, Pi.mul_apply]

private theorem integrable_principal_mul_laplacian
    {A : Fin n → Fin n → ℝ} {v : Spacetime n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v) :
    Integrable (fun z => constantPrincipal A v z * (∑ k, spatialSecond k k v z)) volume := by
  have h := (contDiff_constantPrincipal (A := A) hv).continuous.mul
    (contDiff_laplacian hv).continuous
  exact h.integrable_of_hasCompactSupport
    (hasCompactSupport_constantPrincipal hvc).mul_right

private theorem integrable_principal_sub_mul_laplacian
    {A : Fin n → Fin n → ℝ} {κ : ℝ} {v : Spacetime n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v) :
    Integrable (fun z =>
      (constantPrincipal A v z - κ * (∑ k, spatialSecond k k v z)) ^ 2) volume := by
  have hp : ContDiff ℝ ∞ (fun z => constantPrincipal A v z -
      κ * (∑ k, spatialSecond k k v z)) :=
    (contDiff_constantPrincipal (A := A) hv).sub
      (contDiff_const.mul (contDiff_laplacian hv))
  have hs : HasCompactSupport (fun z => constantPrincipal A v z -
      κ * (∑ k, spatialSecond k k v z)) := by
    exact (hasCompactSupport_constantPrincipal hvc).sub
      (hasCompactSupport_laplacian hvc).mul_left
  have hi := hp.continuous.mul hp.continuous |>.integrable_of_hasCompactSupport
    (μ := (volume : Measure (Spacetime n))) hs.mul_left
  convert hi using 1
  ext z
  simp only [pow_two, Pi.mul_apply]

theorem integral_principal_mul_laplacian_ge
    {A : Fin n → Fin n → ℝ} {κ : ℝ} {v : Spacetime n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v) (_hκ : 0 ≤ κ)
    (hEll : ∀ ξ : Euclid n, κ * ‖ξ‖ ^ 2 ≤
      ∑ i, ∑ j, A i j * ξ i * ξ j) :
    κ * (∫ z, ∑ i, ∑ j, (spatialSecond i j v z) ^ 2) ≤
      ∫ z, constantPrincipal A v z * (∑ k, spatialSecond k k v z) := by
  have hleft : Integrable
      (fun z => κ * (∑ i, ∑ j, (spatialSecond i j v z) ^ 2)) volume := by
    have hi : Integrable (fun z => ∑ i, ∑ j, (spatialSecond i j v z) ^ 2) volume := by
      apply integrable_finsetSum
      intro i hi
      apply integrable_finsetSum
      intro j hj
      exact integrable_spatialSecond_sq hv hvc i j
    exact hi.const_mul κ
  have hterm (k i j : Fin n) :
      Integrable (fun z => A i j * spatialSecond i k v z * spatialSecond j k v z) volume := by
    have hi := integrable_spatialSecond_mul hv hvc i k j k
    have hc := hi.const_mul (A i j)
    exact hc.congr (Filter.Eventually.of_forall (fun z => by ring))
  have hright : Integrable
      (fun z => ∑ k, ∑ i, ∑ j,
        A i j * spatialSecond i k v z * spatialSecond j k v z) volume := by
    apply integrable_finsetSum
    intro k hk
    apply integrable_finsetSum
    intro i hi
    apply integrable_finsetSum
    intro j hj
    exact hterm k i j
  have hpoint : ∀ z,
      κ * (∑ i, ∑ j, (spatialSecond i j v z) ^ 2) ≤
        ∑ k, ∑ i, ∑ j,
          A i j * spatialSecond i k v z * spatialSecond j k v z := by
    intro z
    have hcol (k : Fin n) :
        κ * (∑ i, (spatialSecond i k v z) ^ 2) ≤
          ∑ i, ∑ j, A i j * spatialSecond i k v z * spatialSecond j k v z := by
      have h := hEll (WithLp.toLp 2 (fun i => spatialSecond i k v z))
      simpa only [EuclideanSpace.real_norm_sq_eq, PiLp.toLp_apply] using h
    have hsymm :
        κ * (∑ i, ∑ j, (spatialSecond i j v z) ^ 2) =
          ∑ k, κ * (∑ i, (spatialSecond i k v z) ^ 2) := by
      rw [Finset.sum_comm, Finset.mul_sum]
    rw [hsymm]
    exact Finset.sum_le_sum (fun k hk => hcol k)
  have hmono := integral_mono_ae hleft hright
    (Filter.Eventually.of_forall hpoint)
  have hcross_expand :
      (∫ z, ∑ k, ∑ i, ∑ j,
        A i j * spatialSecond i k v z * spatialSecond j k v z) =
      ∫ z, constantPrincipal A v z * (∑ k, spatialSecond k k v z) := by
    have htriple :
        (∫ z, ∑ k, ∑ i, ∑ j,
          A i j * spatialSecond i k v z * spatialSecond j k v z) =
        ∑ k, ∑ i, ∑ j,
          A i j * (∫ z, spatialSecond i k v z * spatialSecond j k v z) := by
      have hinner (k : Fin n) :
          (∫ z, ∑ i, ∑ j,
            A i j * spatialSecond i k v z * spatialSecond j k v z) =
          ∑ i, ∑ j,
            A i j * (∫ z, spatialSecond i k v z * spatialSecond j k v z) := by
        have hinner2 (i : Fin n) :
          (∫ z, ∑ j, A i j * spatialSecond i k v z * spatialSecond j k v z) =
              ∑ j, A i j * (∫ z, spatialSecond i k v z * spatialSecond j k v z) := by
          convert (integral_finsetSum Finset.univ (fun j hj => hterm k i j)) using 1
          apply Finset.sum_congr rfl
          intro j hj
          rw [← integral_const_mul]
          congr 1
          funext z
          ring
        rw [integral_finsetSum Finset.univ]
        · simp_rw [hinner2]
        · intro i hi
          apply integrable_finsetSum
          intro j hj
          exact hterm k i j
      rw [integral_finsetSum Finset.univ]
      · simp_rw [hinner]
      · intro k hk
        apply integrable_finsetSum
        intro i hi
        apply integrable_finsetSum
        intro j hj
        exact hterm k i j
    calc
      _ = ∑ k, ∑ i, ∑ j,
          A i j * (∫ z, spatialSecond i k v z * spatialSecond j k v z) := htriple
      _ = ∑ k, ∑ i, ∑ j,
          A i j * (∫ z, spatialSecond i j v z * spatialSecond k k v z) := by
        apply Finset.sum_congr rfl
        intro k hk
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        rw [integral_spatialSecond_mul_diag hv hvc i j k]
      _ = ∫ z, constantPrincipal A v z * (∑ k, spatialSecond k k v z) := by
        have hfunc :
            (fun z => constantPrincipal A v z * (∑ k, spatialSecond k k v z)) =
              (fun z => ∑ i, ∑ j, ∑ k,
                A i j * spatialSecond i j v z * spatialSecond k k v z) := by
          funext z
          simp only [constantPrincipal]
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.mul_sum]
        rw [hfunc]
        have htermDiag (i j k : Fin n) :
            Integrable (fun z => A i j * spatialSecond i j v z * spatialSecond k k v z) volume := by
          have hi := (integrable_spatialSecond_mul hv hvc i j k k).const_mul (A i j)
          convert hi using 1
          ext z
          ring
        have hinnerDiag (i j : Fin n) :
            (∫ z, ∑ k, A i j * spatialSecond i j v z * spatialSecond k k v z) =
              ∑ k, A i j * (∫ z, spatialSecond i j v z * spatialSecond k k v z) := by
          convert (integral_finsetSum Finset.univ (fun k hk => htermDiag i j k)) using 1
          apply Finset.sum_congr rfl
          intro k hk
          rw [← integral_const_mul]
          congr 1
          funext z
          ring
        have hinnerDiag' (i : Fin n) :
            (∫ z, ∑ j, ∑ k,
              A i j * spatialSecond i j v z * spatialSecond k k v z) =
              ∑ j, ∑ k, A i j * (∫ z, spatialSecond i j v z * spatialSecond k k v z) := by
          have hinnerJ (j : Fin n) := hinnerDiag i j
          have hsumJ (j : Fin n) :
              Integrable (fun z => ∑ k,
                A i j * spatialSecond i j v z * spatialSecond k k v z) volume := by
            apply integrable_finsetSum
            intro k hk
            exact htermDiag i j k
          convert (integral_finsetSum Finset.univ
            (fun j hj => hsumJ j)) using 1
          simp_rw [hinnerJ]
        have hsumI (i : Fin n) :
            Integrable (fun z => ∑ j, ∑ k,
              A i j * spatialSecond i j v z * spatialSecond k k v z) volume := by
          apply integrable_finsetSum
          intro j hj
          apply integrable_finsetSum
          intro k hk
          exact htermDiag i j k
        have hout := integral_finsetSum Finset.univ (fun i hi => hsumI i)
        have hfinal :
            (∫ z, ∑ i, ∑ j, ∑ k,
              A i j * spatialSecond i j v z * spatialSecond k k v z) =
              ∑ i, ∑ j, ∑ k,
                A i j * (∫ z, spatialSecond i j v z * spatialSecond k k v z) := by
          calc
            _ = ∑ i, ∫ z, ∑ j, ∑ k,
                A i j * spatialSecond i j v z * spatialSecond k k v z := hout
            _ = ∑ i, ∑ j, ∑ k,
                A i j * (∫ z, spatialSecond i j v z * spatialSecond k k v z) := by
              apply Finset.sum_congr rfl
              intro i hi
              exact hinnerDiag' i
        calc
          _ = ∑ i, ∑ k, ∑ j,
              A i j * (∫ z, spatialSecond i j v z * spatialSecond k k v z) := by
            rw [Finset.sum_comm]
          _ = ∑ i, ∑ j, ∑ k,
              A i j * (∫ z, spatialSecond i j v z * spatialSecond k k v z) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.sum_comm]
          _ = _ := hfinal.symm
  rw [hcross_expand] at hmono
  simpa only [integral_const_mul] using hmono

theorem integral_principal_sq_ge
    {A : Fin n → Fin n → ℝ} {κ : ℝ} {v : Spacetime n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v) (hκ : 0 ≤ κ)
    (hEll : ∀ ξ : Euclid n, κ * ‖ξ‖ ^ 2 ≤
      ∑ i, ∑ j, A i j * ξ i * ξ j) :
    κ ^ 2 * (∫ z, ∑ i, ∑ j, (spatialSecond i j v z) ^ 2) ≤
      ∫ z, (constantPrincipal A v z) ^ 2 := by
  have hLsq := integrable_constantPrincipal_sq (A := A) hv hvc
  have hDsq := integrable_laplacian_sq hv hvc
  have hcross := integrable_principal_mul_laplacian (A := A) hv hvc
  have hdiff := integrable_principal_sub_mul_laplacian (A := A) (κ := κ) hv hvc
  have hcross2 := hcross.const_mul (2 * κ)
  have hD2 := hDsq.const_mul (κ ^ 2)
  have hsub : Integrable (fun z => (constantPrincipal A v z) ^ 2 -
      (2 * κ) * (constantPrincipal A v z * (∑ k, spatialSecond k k v z))) volume := by
    have hi := hLsq.sub hcross2
    exact hi.congr (Filter.Eventually.of_forall (fun z => by rfl))
  have hexpand :
      (∫ z, (constantPrincipal A v z - κ * (∑ k, spatialSecond k k v z)) ^ 2) =
        (∫ z, (constantPrincipal A v z) ^ 2) -
          2 * κ * (∫ z, constantPrincipal A v z * (∑ k, spatialSecond k k v z)) +
          κ ^ 2 * (∫ z, (∑ k, spatialSecond k k v z) ^ 2) := by
    have hpoint :
        (fun z => (constantPrincipal A v z - κ * (∑ k, spatialSecond k k v z)) ^ 2) =
          (fun z => (constantPrincipal A v z) ^ 2 -
            (2 * κ) * (constantPrincipal A v z * (∑ k, spatialSecond k k v z)) +
            κ ^ 2 * (∑ k, spatialSecond k k v z) ^ 2) := by
      funext z
      ring
    rw [hpoint]
    rw [integral_add hsub hD2,
      integral_sub hLsq hcross2, integral_const_mul, integral_const_mul]
  have hnonneg :
      0 ≤ (∫ z, (constantPrincipal A v z - κ * (∑ k, spatialSecond k k v z)) ^ 2) := by
    apply integral_nonneg
    intro z
    exact sq_nonneg _
  have hcross_ge := integral_principal_mul_laplacian_ge hv hvc hκ hEll
  have hdiag := integral_laplacian_sq_eq_hessian hv hvc
  rw [hexpand, hdiag] at hnonneg
  nlinarith

end Poincare.Analysis.Parabolic.WeakRegularity.Canonical
