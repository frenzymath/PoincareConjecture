import PoincareConjecture.Definitions.Ch01.RiemannianMetric
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame








set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators Topology

open Filter

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] {g : RiemannianMetric n M}

theorem connection_finset_sum (D : LeviCivitaData g) {ι : Type*} (S : Finset ι)
    (σ : ι → (q : M) → TangentSpace (𝓡 n) q) (q : M)
    (hσ : ∀ i ∈ S, MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) (T% (σ i)) q)
    (X : TangentSpace (𝓡 n) q) :
    D.connection (fun x ↦ ∑ i ∈ S, σ i x) q X = ∑ i ∈ S, D.connection (σ i) q X := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact congrArg (fun f : (x : M) → TangentSpace (𝓡 n) x →L[ℝ]
        TangentSpace (𝓡 n) x ↦ f q X) D.connection.zero
  | insert a S ha ih =>
      simp only [Finset.mem_insert, forall_eq_or_imp] at hσ
      simp only [Finset.sum_insert ha]
      change D.connection (σ a + (fun x ↦ ∑ i ∈ S, σ i x)) q X = _
      rw [D.connection.isCovariantDerivativeOnUniv.add hσ.1
        (MDifferentiableAt.sum_section hσ.2)]
      simp only [add_apply]
      rw [ih hσ.2]

theorem connection_germ_expansion (D : LeviCivitaData g) {ι : Type*} [Fintype ι]
    (σ : (q : M) → TangentSpace (𝓡 n) q)
    (frame : ι → (q : M) → TangentSpace (𝓡 n) q) (c : ι → M → ℝ)
    (q : M) (X : TangentSpace (𝓡 n) q)
    (hσ : MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) (T% σ) q)
    (hframe : ∀ i, MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) (T% (frame i)) q)
    (hc : ∀ i, MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ)) (c i) q)
    (heq : σ =ᶠ[𝓝 q] (fun x ↦ ∑ i, c i x • frame i x)) :
    D.connection σ q X =
      ∑ i, (c i q • D.connection (frame i) q X +
        mvfderiv (𝓡 n) (c i) q X • frame i q) := by
  have hterm (i : ι) := (hc i).smul_section (hframe i)
  have hcongr := D.connection.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    hσ (MDifferentiableAt.sum_section (fun i _ ↦ hterm i)) (by simp) heq
  rw [hcongr, connection_finset_sum D Finset.univ _ q (fun i _ ↦ hterm i)]
  apply Finset.sum_congr rfl
  intro i _
  change D.connection ((c i) • frame i) q X = _
  rw [D.connection.isCovariantDerivativeOnUniv.leibniz (hframe i) (hc i)]
  rfl

theorem connection_localFrame (D : LeviCivitaData g) {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ (EuclideanSpace ℝ (Fin n))) (p q : M)
    (hq : q ∈ (trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) p).baseSet)
    (σ : (x : M) → TangentSpace (𝓡 n) x)
    (hσ : MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) (T% σ) q)
    (X : TangentSpace (𝓡 n) q) :
    let e := trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) p
    D.connection σ q X = ∑ i,
      ((e.localFrameCoeff (𝓡 n) b i q (σ q)) • D.connection (e.localFrame b i) q X +
        mvfderiv (𝓡 n) (fun x ↦ e.localFrameCoeff (𝓡 n) b i x (σ x)) q X •
          e.localFrame b i q) := by
  let e := trivializationAt (EuclideanSpace ℝ (Fin n))
    (TangentSpace (𝓡 n) : M → Type _) p
  apply connection_germ_expansion D σ (e.localFrame b)
    (fun i x ↦ e.localFrameCoeff (𝓡 n) b i x (σ x)) q X hσ
  · intro i
    exact (contMDiffAt_localFrame_of_mem 1 e b i hq).mdifferentiableAt (by simp)
  · intro i
    exact mdifferentiableAt_localFrameCoeff b hq hσ i
  · exact e.eventually_eq_localFrame_sum_coeff_smul b hq

end PoincareConjecture.Proofs.M09
