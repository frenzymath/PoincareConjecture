import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Iteration.WeakEquation








noncomputable section

open Set MeasureTheory Function Filter Topology
open scoped ENNReal ContDiff

namespace Poincare.Analysis.Elliptic.Iteration

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

def matrixFlux (A : E → Matrix (Fin n) (Fin n) ℝ) (p : Fin n → E → ℝ) :
    Fin n → E → ℝ := fun i x => ∑ j, A x i j * p j x

theorem matrixFlux_congr_ae {O : Set E} (A : E → Matrix (Fin n) (Fin n) ℝ)
    {p q : Fin n → E → ℝ} (hpq : ∀ i, p i =ᵐ[volume.restrict O] q i) (i : Fin n) :
    matrixFlux A p i =ᵐ[volume.restrict O] matrixFlux A q i := by
  filter_upwards [ae_all_iff.mpr hpq] with x hx
  exact Finset.sum_congr rfl (fun j _ => by rw [hx j])

def differentiatedSource (A : E → Matrix (Fin n) (Fin n) ℝ)
    (p : Fin n → E → ℝ) (q : Fin n → Fin n → E → ℝ)
    (g : E → ℝ) (k : Fin n) : E → ℝ := fun x =>
  g x + ∑ i, ∑ j, (
    (partialDeriv k (fun y => A y i j) x) * q i j x +
      (partialDeriv i (partialDeriv k (fun y => A y i j)) x) * p j x)

theorem locallyIntegrable_matrixFlux
    {O : Set E} {A : E → Matrix (Fin n) (Fin n) ℝ} {p : Fin n → E → ℝ}
    (hA : ∀ i j, Continuous (fun x => A x i j))
    (hp : ∀ j, LocallyIntegrable (p j) (volume.restrict O)) (i : Fin n) :
    LocallyIntegrable (matrixFlux A p i) (volume.restrict O) :=
  locallyIntegrable_finset_sum Finset.univ (fun j _ =>
    LocallyIntegrable.continuous_mul (hA i j) (hp j))

theorem differentiated_equation
    {O : Set E} (hO : IsOpen O)
    {A : E → Matrix (Fin n) (Fin n) ℝ} {p : Fin n → E → ℝ}
    {q : Fin n → Fin n → E → ℝ} {f g : E → ℝ} (k : Fin n)
    (hA : ∀ i j, ContDiff ℝ ∞ (fun x => A x i j))
    (hp : ∀ j, LocallyIntegrable (p j) (volume.restrict O))
    (hq : ∀ i j, LocallyIntegrable (q i j) (volume.restrict O))
    (hg : LocallyIntegrable g (volume.restrict O))
    (hpq : ∀ i j, Sobolev.Weak.HasWeakPartialDeriv i (q i j) (p j) O)
    (hfg : Sobolev.Weak.HasWeakPartialDeriv k g f O)
    (heq : WeakEquation O (matrixFlux A p) f) :
    WeakEquation O (matrixFlux A (q k)) (differentiatedSource A p q g k) := by
  let F := matrixFlux A (q k)
  let H : Fin n → E → ℝ := fun i x =>
    ∑ j, partialDeriv k (fun y => A y i j) x * p j x
  let S : Fin n → E → ℝ := fun i x =>
    ∑ j, (partialDeriv k (fun y => A y i j) x * q i j x +
      partialDeriv i (partialDeriv k (fun y => A y i j)) x * p j x)
  have hF i : LocallyIntegrable (F i) (volume.restrict O) :=
    locallyIntegrable_matrixFlux (fun i j => (hA i j).continuous) (hq k) i
  have hH i : LocallyIntegrable (H i) (volume.restrict O) :=
    locallyIntegrable_finset_sum Finset.univ (fun j _ =>
      LocallyIntegrable.continuous_mul (contDiff_partial (hA i j) k).continuous (hp j))
  have hS i : LocallyIntegrable (S i) (volume.restrict O) :=
    locallyIntegrable_finset_sum Finset.univ (fun j _ =>
      (LocallyIntegrable.continuous_mul (contDiff_partial (hA i j) k).continuous
        (hq i j)).add
      (LocallyIntegrable.continuous_mul
        (contDiff_partial (contDiff_partial (hA i j) k) i).continuous (hp j)))
  have hdiff : WeakEquation O (fun i x => F i x + H i x) g := by
    apply heq.differentiate
      (fun i => locallyIntegrable_matrixFlux (fun i j => (hA i j).continuous) hp i)
      (fun i => (hF i).add (hH i)) _ hfg
    intro i
    have hw := weakPartial_finset_sum Finset.univ
      (fun j _ => LocallyIntegrable.continuous_mul (hA i j).continuous (hp j))
      (fun j _ => (LocallyIntegrable.continuous_mul (hA i j).continuous (hq k j)).add
        (LocallyIntegrable.continuous_mul (contDiff_partial (hA i j) k).continuous (hp j)))
      (fun j _ => (hpq k j).mul_smooth hO (hA i j) (hp j) (hq k j))
    change Sobolev.Weak.HasWeakPartialDeriv k
      (fun x => (∑ j, A x i j * q k j x) +
        (∑ j, partialDeriv k (fun y => A y i j) x * p j x))
      (fun x => ∑ j, A x i j * p j x) O
    simpa only [Pi.add_apply, Finset.sum_add_distrib, partialDeriv] using hw
  apply hdiff.remove_flux hF hH hS hg
  intro i
  exact weakPartial_finset_sum Finset.univ
    (fun j _ => LocallyIntegrable.continuous_mul (contDiff_partial (hA i j) k).continuous (hp j))
    (fun j _ => (LocallyIntegrable.continuous_mul (contDiff_partial (hA i j) k).continuous
      (hq i j)).add (LocallyIntegrable.continuous_mul
      (contDiff_partial (contDiff_partial (hA i j) k) i).continuous (hp j)))
    (fun j _ => (hpq i j).mul_smooth hO (contDiff_partial (hA i j) k) (hp j) (hq i j))


theorem weakGradient_of_weakHessian
    {O : Set E} (hO : IsOpen O) {u : E → ℝ} {p : Fin n → E → ℝ}
    {q : Fin n → Fin n → E → ℝ}
    (hp : ∀ i, Sobolev.Weak.HasWeakPartialDeriv i (p i) u O)
    (hq : ∀ i j, Sobolev.Weak.HasWeakPartialDeriv i (q i j) (p j) O)
    (hqint : ∀ i j, LocallyIntegrable (q i j) (volume.restrict O)) (k j : Fin n) :
    Sobolev.Weak.HasWeakPartialDeriv j (q k j) (p k) O := by
  have heq := weakPartial_comm_ae hO (hp j) (hp k) (hq k j) (hq j k)
    (hqint k j) (hqint j k)
  intro φ hφ hφc hφO
  rw [hq j k φ hφ hφc hφO]
  congr 1
  apply integral_congr_ae
  filter_upwards [heq] with x hx
  rw [hx]

end Poincare.Analysis.Elliptic.Iteration
