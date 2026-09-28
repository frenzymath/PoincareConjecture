




import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.CanonicalEquation
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.Variation.Coordinates
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.ConstantEnergyCross
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace










open MeasureTheory Set
open scoped ContDiff Topology

noncomputable section

namespace Poincare.Analysis.Parabolic.WeakRegularity.Canonical

variable {n : ℕ}

local instance : (volume : Measure (Spacetime n)).IsAddHaarMeasure := by
  change ((volume : Measure (Euclid n)).prod (volume : Measure ℝ)).IsAddHaarMeasure
  infer_instance

theorem integral_directionalDeriv_mul_eq_neg
    {f g : Spacetime n → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) (w : Spacetime n) :
    (∫ z, fderiv ℝ f z w * g z) = -(∫ z, f z * fderiv ℝ g z w) := by
  have hprod : ContDiff ℝ ∞ (fun z => f z * g z) := hf.mul hg
  have hprod_c : HasCompactSupport (fun z => f z * g z) := by
    change HasCompactSupport (f * g)
    exact hfc.mul_right
  have hz := integral_fderiv_eq_zero_of_contDiff_compactSupport hprod hprod_c w
  have hdf : ∀ z, fderiv ℝ (fun y => f y * g y) z w =
      fderiv ℝ f z w * g z + f z * fderiv ℝ g z w := by
    intro z
    change (fderiv ℝ (f * g) z) w = _
    have hmul := (hf.differentiable (by simp) z).hasFDerivAt.mul
      (hg.differentiable (by simp) z).hasFDerivAt
    rw [hmul.fderiv]
    simp [smul_eq_mul]
    ring
  rw [show (fun z => fderiv ℝ (fun y => f y * g y) z w) =
      (fun z => fderiv ℝ f z w * g z + f z * fderiv ℝ g z w) by funext z; exact hdf z] at hz
  have hleft : Integrable (fun z => fderiv ℝ f z w * g z) volume := by
    apply (((hf.fderiv_right (m := ∞) (n := ∞) (by simp)).clm_apply contDiff_const).continuous.mul hg.continuous).integrable_of_hasCompactSupport
    simpa only [Pi.mul_apply] using (hfc.fderiv_apply ℝ w).mul_right (f' := g)
  have hright : Integrable (fun z => f z * fderiv ℝ g z w) volume := by
    apply (hf.continuous.mul ((hg.fderiv_right (m := ∞) (n := ∞) (by simp)).clm_apply contDiff_const).continuous).integrable_of_hasCompactSupport
    simpa only [Pi.mul_apply] using (hgc.fderiv_apply ℝ w).mul_left (f := f)
  rw [integral_add hleft hright] at hz
  linarith [hz]


def spatialSecond (i j : Fin n) (v : Spacetime n → ℝ) : Spacetime n → ℝ :=
  spatialDeriv i (spatialDeriv j v)


def constantPrincipal (A : Fin n → Fin n → ℝ) (v : Spacetime n → ℝ)
    (z : Spacetime n) : ℝ :=
  ∑ i, ∑ j, A i j * spatialSecond i j v z


theorem spatialSecond_comm (v : Spacetime n → ℝ) (hv : ContDiff ℝ ∞ v)
    (i j : Fin n) (z : Spacetime n) :
    spatialDeriv i (spatialDeriv j v) z = spatialDeriv j (spatialDeriv i v) z := by
  have h := PoincareConjecture.ConnectionVariation.covDerivAlong_fderiv_symm (Γ := fun _ => 0)
    (u := v) (p := z) (hv.contDiffAt.of_le (show (2 : ℕ∞ω) ≤ ∞ by norm_cast))
    (fun X Y => by simp) (spatialDirection i) (spatialDirection j)
  change fderiv ℝ (fun y => fderiv ℝ v y (spatialDirection j)) z
      (spatialDirection i) =
    fderiv ℝ (fun y => fderiv ℝ v y (spatialDirection i)) z
      (spatialDirection j)
  simpa [PoincareConjecture.ConnectionVariation.covDerivAlong] using h



theorem hasCompactSupport_spatialSecond
    {v : Spacetime n → ℝ} (i j : Fin n) (hvc : HasCompactSupport v) :
    HasCompactSupport (spatialSecond i j v) := by
  exact hvc.fderiv_apply ℝ (spatialDirection j) |>.fderiv_apply ℝ (spatialDirection i)

theorem contDiff_spatialSecond {v : Spacetime n → ℝ} (hv : ContDiff ℝ ∞ v)
    (i j : Fin n) : ContDiff ℝ ∞ (spatialSecond i j v) := by
  have h₁ : ContDiff ℝ ∞ (fun z => fderiv ℝ v z (spatialDirection j)) :=
    (hv.fderiv_right (m := ∞) (n := ∞) (by simp)).clm_apply contDiff_const
  have h₂ : ContDiff ℝ ∞ (fun z => fderiv ℝ (fun y => fderiv ℝ v y
      (spatialDirection j)) z (spatialDirection i)) :=
    (h₁.fderiv_right (m := ∞) (n := ∞) (by simp)).clm_apply contDiff_const
  exact h₂

theorem hasCompactSupport_spatialDeriv
    {v : Spacetime n → ℝ} (i : Fin n) (hvc : HasCompactSupport v) :
    HasCompactSupport (spatialDeriv i v) :=
  hvc.fderiv_apply ℝ (spatialDirection i)

theorem contDiff_spatialDeriv {v : Spacetime n → ℝ} (hv : ContDiff ℝ ∞ v)
    (i : Fin n) : ContDiff ℝ ∞ (spatialDeriv i v) := by
  exact (hv.fderiv_right (m := ∞) (n := ∞) (by simp)).clm_apply contDiff_const

theorem directionalSecond_comm (v : Spacetime n → ℝ) (hv : ContDiff ℝ ∞ v)
    (w₁ w₂ : Spacetime n) (z : Spacetime n) :
    fderiv ℝ (fun y => fderiv ℝ v y w₂) z w₁ =
      fderiv ℝ (fun y => fderiv ℝ v y w₁) z w₂ := by
  have h := PoincareConjecture.ConnectionVariation.covDerivAlong_fderiv_symm (Γ := fun _ => 0)
    (u := v) (p := z) (hv.contDiffAt.of_le (show (2 : ℕ∞ω) ≤ ∞ by norm_cast))
    (fun X Y => by simp) w₁ w₂
  change fderiv ℝ (fun y => fderiv ℝ v y w₂) z w₁ =
      fderiv ℝ (fun y => fderiv ℝ v y w₁) z w₂
  simpa [PoincareConjecture.ConnectionVariation.covDerivAlong] using h

theorem integral_spatialSecond_mul_diag
    {v : Spacetime n → ℝ} (hv : ContDiff ℝ ∞ v)
    (hvc : HasCompactSupport v) (i j k : Fin n) :
    (∫ z, spatialSecond i j v z * spatialSecond k k v z) =
      ∫ z, spatialSecond i k v z * spatialSecond j k v z := by
  let f : Spacetime n → ℝ := spatialSecond i j v
  let g : Spacetime n → ℝ := spatialDeriv k v
  have hf : ContDiff ℝ ∞ f := contDiff_spatialSecond hv i j
  have hg : ContDiff ℝ ∞ g := contDiff_spatialDeriv hv k
  have hfc : HasCompactSupport f := hasCompactSupport_spatialSecond i j hvc
  have hgc : HasCompactSupport g := hasCompactSupport_spatialDeriv k hvc
  have h₁ := integral_directionalDeriv_mul_eq_neg hf hfc hg hgc (spatialDirection k)
  have h₂ := integral_directionalDeriv_mul_eq_neg
    (contDiff_spatialSecond hv i k) (hasCompactSupport_spatialSecond i k hvc)
    hg hgc (spatialDirection j)
  have hcomm : ∀ z, spatialDeriv k (spatialSecond i j v) z =
      spatialDeriv j (spatialSecond i k v) z := by
    intro z
    change fderiv ℝ (fun y => fderiv ℝ (fun x => fderiv ℝ v x
      (spatialDirection j)) y (spatialDirection i)) z (spatialDirection k) =
      fderiv ℝ (fun y => fderiv ℝ (fun x => fderiv ℝ v x
        (spatialDirection k)) y (spatialDirection i)) z (spatialDirection j)
    have hki := directionalSecond_comm (spatialDeriv j v) (contDiff_spatialDeriv hv j)
      (spatialDirection k) (spatialDirection i) z
    change fderiv ℝ (fun y => fderiv ℝ (fun x => fderiv ℝ v x
      (spatialDirection j)) y (spatialDirection i)) z (spatialDirection k) =
      fderiv ℝ (fun y => fderiv ℝ (fun x => fderiv ℝ v x
        (spatialDirection j)) y (spatialDirection k)) z (spatialDirection i) at hki
    have hkj : (fun y => fderiv ℝ (fun x => fderiv ℝ v x
        (spatialDirection j)) y (spatialDirection k)) =
        (fun y => fderiv ℝ (fun x => fderiv ℝ v x
          (spatialDirection k)) y (spatialDirection j)) := by
      funext y
      exact directionalSecond_comm v hv
        (spatialDirection k) (spatialDirection j) y
    have hij := directionalSecond_comm (spatialDeriv k v) (contDiff_spatialDeriv hv k)
      (spatialDirection i) (spatialDirection j) z
    rw [hkj] at hki
    exact hki.trans hij
  have h₁' : (∫ z, spatialDeriv k (spatialSecond i j v) z * spatialDeriv k v z) =
      -(∫ z, spatialSecond i j v z * spatialSecond k k v z) := by
    exact h₁
  have h₂' : (∫ z, spatialDeriv j (spatialSecond i k v) z * spatialDeriv k v z) =
      -(∫ z, spatialSecond i k v z * spatialSecond j k v z) := by
    exact h₂
  rw [show (fun z => spatialDeriv k (spatialSecond i j v) z * spatialDeriv k v z) =
      (fun z => spatialDeriv j (spatialSecond i k v) z * spatialDeriv k v z) by
        funext z; rw [hcomm z]] at h₁'
  linarith [h₁', h₂']

theorem hasCompactSupport_timeDeriv
    {v : Spacetime n → ℝ} (hvc : HasCompactSupport v) :
    HasCompactSupport (timeDeriv v) :=
  hvc.fderiv_apply ℝ (0, 1)

theorem contDiff_timeDeriv {v : Spacetime n → ℝ} (hv : ContDiff ℝ ∞ v) :
    ContDiff ℝ ∞ (timeDeriv v) := by
  exact (hv.fderiv_right (m := ∞) (n := ∞) (by simp)).clm_apply contDiff_const

theorem hasCompactSupport_constantPrincipal
    {A : Fin n → Fin n → ℝ} {v : Spacetime n → ℝ}
    (hvc : HasCompactSupport v) :
    HasCompactSupport (constantPrincipal A v) := by
  classical
  have hterm (i : Fin n) (j : Fin n) :
      HasCompactSupport (fun z => A i j * spatialSecond i j v z) :=
    (hasCompactSupport_spatialSecond i j hvc).mul_left
  have hinner (i : Fin n) :
      HasCompactSupport (fun z => ∑ j, A i j * spatialSecond i j v z) := by
    have hsum : ∀ s : Finset (Fin n),
        HasCompactSupport (fun z => s.sum (fun j => A i j * spatialSecond i j v z)) := by
      intro s
      induction s using Finset.induction_on with
      | empty => exact HasCompactSupport.zero
      | @insert j s hjs ih =>
        simp only [Finset.sum_insert hjs]
        exact (hterm i j).add ih
    simpa using hsum Finset.univ
  have hsum : ∀ s : Finset (Fin n),
      HasCompactSupport (fun z => s.sum (fun i => ∑ j, A i j * spatialSecond i j v z)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact HasCompactSupport.zero
    | @insert i s his ih =>
      simp only [Finset.sum_insert his]
      exact (hinner i).add ih
  change HasCompactSupport (fun z => ∑ i, ∑ j, A i j * spatialSecond i j v z)
  exact hsum Finset.univ

theorem contDiff_constantPrincipal
    {A : Fin n → Fin n → ℝ} {v : Spacetime n → ℝ}
    (hv : ContDiff ℝ ∞ v) :
    ContDiff ℝ ∞ (constantPrincipal A v) := by
  have hterm (i : Fin n) (j : Fin n) :
      ContDiff ℝ ∞ (fun z => A i j * spatialSecond i j v z) := by
    exact contDiff_const.mul (contDiff_spatialSecond hv i j)
  have hinner (i : Fin n) :
      ContDiff ℝ ∞ (fun z => ∑ j, A i j * spatialSecond i j v z) :=
    ContDiff.sum (fun j _ => hterm i j)
  change ContDiff ℝ ∞ (fun z => ∑ i, ∑ j, A i j * spatialSecond i j v z)
  exact ContDiff.sum (fun i _ => hinner i)

theorem integrable_timeDeriv_sq
    {v : Spacetime n → ℝ} (hv : ContDiff ℝ ∞ v)
    (hvc : HasCompactSupport v) :
    Integrable (fun z => (timeDeriv v z) ^ 2) volume := by
  have hcont := (contDiff_timeDeriv hv).continuous.mul (contDiff_timeDeriv hv).continuous
  have hsupp : HasCompactSupport (timeDeriv v * timeDeriv v) :=
    (hasCompactSupport_timeDeriv hvc).mul_left
  have hI := hcont.integrable_of_hasCompactSupport (μ := volume) hsupp
  convert hI using 1
  ext z
  simp only [pow_two, Pi.mul_apply]

theorem integrable_constantPrincipal_sq
    {A : Fin n → Fin n → ℝ} {v : Spacetime n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v) :
    Integrable (fun z => (constantPrincipal A v z) ^ 2) volume := by
  have hcont := (contDiff_constantPrincipal (A := A) hv).continuous.mul
    (contDiff_constantPrincipal (A := A) hv).continuous
  have hsupp : HasCompactSupport (constantPrincipal A v * constantPrincipal A v) :=
    (hasCompactSupport_constantPrincipal hvc).mul_left
  have hI := hcont.integrable_of_hasCompactSupport (μ := volume) hsupp
  convert hI using 1
  ext z
  simp only [pow_two, Pi.mul_apply]

theorem integrable_timeDeriv_mul_constantPrincipal
    {A : Fin n → Fin n → ℝ} {v : Spacetime n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v) :
    Integrable (fun z => timeDeriv v z * constantPrincipal A v z) volume := by
  have hcont := (contDiff_timeDeriv hv).continuous.mul
    (contDiff_constantPrincipal (A := A) hv).continuous
  have hsupp : HasCompactSupport ((timeDeriv v) * (constantPrincipal A v)) := by
    exact (hasCompactSupport_timeDeriv hvc).mul_right
  exact hcont.integrable_of_hasCompactSupport (μ := volume) hsupp

theorem integrable_mul_spatialSecond
    {v : Spacetime n → ℝ} (hv : ContDiff ℝ ∞ v)
    (hvc : HasCompactSupport v) (i j : Fin n) :
    Integrable (fun z => timeDeriv v z * spatialSecond i j v z) volume := by
  apply ((hv.fderiv_right (m := ∞) (n := ∞) (by simp)).clm_apply contDiff_const).continuous.mul
    (contDiff_spatialSecond hv i j).continuous |>.integrable_of_hasCompactSupport
  have hsc : HasCompactSupport (spatialSecond i j v) :=
    hasCompactSupport_spatialSecond i j hvc
  exact hsc.mul_left

theorem integrable_spatialSecond_sq
    {v : Spacetime n → ℝ} (hv : ContDiff ℝ ∞ v)
    (hvc : HasCompactSupport v) (i j : Fin n) :
    Integrable (fun z => (spatialSecond i j v z) ^ 2) volume := by
  have hcont := (contDiff_spatialSecond hv i j).continuous.mul
    (contDiff_spatialSecond hv i j).continuous
  have hsupp : HasCompactSupport (spatialSecond i j v * spatialSecond i j v) :=
    (hasCompactSupport_spatialSecond i j hvc).mul_left
  have hI := hcont.integrable_of_hasCompactSupport (μ := volume) hsupp
  convert hI using 1
  ext z
  simp only [pow_two, Pi.mul_apply]

end Poincare.Analysis.Parabolic.WeakRegularity.Canonical
