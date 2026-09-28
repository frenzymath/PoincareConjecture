import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.InteriorH2
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Iteration.DifferentiatedEquation
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Iteration.LocalSobolev
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Iteration.LocalL2

noncomputable section

open Set MeasureTheory
open scoped ENNReal ContDiff
open Poincare.Analysis.Sobolev.Weak
open Poincare.Analysis.Sobolev.Euclidean

namespace Poincare.Analysis.Elliptic.Iteration

variable {n : ℕ} [NeZero n]
local notation "E" => EuclideanSpace ℝ (Fin n)

omit [NeZero n] in
theorem memWkpLocally_differentiatedSource
    {O : Set E} (hO : IsOpen O) {m : ℕ}
    {A : E → Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j, ContDiff ℝ ∞ (fun x => A x i j))
    {p : Fin n → E → ℝ} {q : Fin n → Fin n → E → ℝ} {g : E → ℝ}
    (hp : ∀ j, MemWkpLocally m (p j) O)
    (hq : ∀ i j, MemWkpLocally m (q i j) O)
    (hg : MemWkpLocally m g O) (k : Fin n) :
    MemWkpLocally m (differentiatedSource A p q g k) O := by
  apply hg.add
  apply MemWkpLocally.sum hO Finset.univ
  intro i _
  apply MemWkpLocally.sum hO Finset.univ
  intro j _
  exact ((hq i j).smooth_mul (contDiff_partial (hA i j) k)).add
    ((hp j).smooth_mul (contDiff_partial (contDiff_partial (hA i j) k) i))

theorem memWkpLocally_add_two_of_weakEquation (k : ℕ)
    {O : Set E} (hO : IsOpen O)
    {A : E → Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j, ContDiff ℝ ∞ (fun x => A x i j))
    (hpos : ∀ x ∈ O, (A x).PosDef)
    {u f : E → ℝ} {p : Fin n → E → ℝ}
    (hu : MemLp u 2 (volume.restrict O))
    (hp : ∀ i, MemLp (p i) 2 (volume.restrict O))
    (hpartial : ∀ i, HasWeakPartialDeriv i (p i) u O)
    (hf : MemWkpLocally k f O)
    (heq : WeakEquation O (matrixFlux A p) f) :
    MemWkpLocally (k + 2) u O := by
  induction k generalizing O u f p with
  | zero =>
      intro x hx
      apply exists_memWkp_two_of_weakEquation hO A u f p
        (fun i j => (hA i j).contDiffOn) hpos
        (fun K _ hKO => hu.mono_measure (Measure.restrict_mono hKO le_rfl))
        (fun i K _ hKO => (hp i).mono_measure (Measure.restrict_mono hKO le_rfl))
        (compact_memLp_of_local_memLp hf) hpartial _ hx
      intro φ hφ hφc hφO
      simpa only [matrixFlux, partialDeriv, Finset.sum_mul] using heq φ hφ hφc hφO
  | succ k ih =>
      have hureg := ih hO hpos hu hp hpartial (hf.mono_order (Nat.le_succ k)) heq
      intro x hx
      obtain ⟨U, hU, hxU, hUO, huU⟩ := hureg x hx
      obtain ⟨V, hV, hxV, _, hfV⟩ := hf x hx
      let W := U ∩ V
      have hW : IsOpen W := hU.inter hV
      have hWO : W ⊆ O := inter_subset_left.trans hUO
      have huW : MemWkp (k + 2) 2 u W :=
        huU.mono_set (by norm_num) hW inter_subset_left
      have hfW : MemWkp (k + 1) 2 f W :=
        hfV.mono_set (by norm_num) hW inter_subset_right
      let P : Fin n → E → ℝ := fun i => chosenWeakPartial' 2 i u W
      let Q : Fin n → Fin n → E → ℝ := fun i j => chosenWeakPartial' 2 i (P j) W
      let G : Fin n → E → ℝ := fun i => chosenWeakPartial' 2 i f W
      have hP (i) : MemWkp (k + 1) 2 (P i) W := huW.chosenWeakPartial_mem i
      have hQ (i j) : MemWkp k 2 (Q i j) W := (hP j).chosenWeakPartial_mem i
      have hG (i) : MemWkp k 2 (G i) W := hfW.chosenWeakPartial_mem i
      have hwP (i) : HasWeakPartialDeriv i (P i) u W :=
        chosenWeakPartial'_isWeakPartial_of_mem huW.memW1p i
      have hwQ (i j) : HasWeakPartialDeriv i (Q i j) (P j) W :=
        chosenWeakPartial'_isWeakPartial_of_mem (hP j).memW1p i
      have hwG (i) : HasWeakPartialDeriv i (G i) f W :=
        chosenWeakPartial'_isWeakPartial_of_mem hfW.memW1p i
      have hpP (i) : p i =ᵐ[volume.restrict W] P i :=
        HasWeakPartialDeriv.ae_eq hW ((hpartial i).restrict hW hWO) (hwP i)
          (((hp i).mono_measure (Measure.restrict_mono hWO le_rfl)).locallyIntegrable
            (by norm_num)) ((hP i).memLp.locallyIntegrable (by norm_num))
      have heqW : WeakEquation W (matrixFlux A P) f :=
        (heq.restrict hWO).congr_flux (matrixFlux_congr_ae A hpP)
      have hPint i := (hP i).memLp.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      have hQint i j := (hQ i j).memLp.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      have hPreg (i) : MemWkpLocally (k + 2) (P i) W := by
        apply ih hW (fun y hy => hpos y (hWO hy)) (hP i).memLp
          (fun j => (hQ i j).memLp)
          (weakGradient_of_weakHessian hW hwP hwQ hQint i)
        · exact memWkpLocally_differentiatedSource hW hA
            (fun j => locally_of_memWkp hW (hP j).le_succ)
            (fun a b => locally_of_memWkp hW (hQ a b))
            (locally_of_memWkp hW (hG i)) i
        · exact differentiated_equation hW i hA hPint hQint
            ((hG i).memLp.locallyIntegrable (by norm_num)) hwQ (hwG i) heqW
      have hresult := memWkpLocally_succ_of_weakDerivatives hW
        (locally_of_memWkp hW (k := 0) huW.memLp) hPreg hwP
      obtain ⟨Z, hZ, hxZ, hZW, huZ⟩ := hresult x ⟨hxU, hxV⟩
      exact ⟨Z, hZ, hxZ, hZW.trans hWO, huZ⟩

theorem memWkpLocally_all_of_weakEigenfunction
    {O : Set E} (hO : IsOpen O)
    {A : E → Matrix (Fin n) (Fin n) ℝ} {c u : E → ℝ} {p : Fin n → E → ℝ}
    (hA : ∀ i j, ContDiff ℝ ∞ (fun x => A x i j))
    (hpos : ∀ x ∈ O, (A x).PosDef) (hc : ContDiff ℝ ∞ c)
    (hu : MemLp u 2 (volume.restrict O))
    (hp : ∀ i, MemLp (p i) 2 (volume.restrict O))
    (hpartial : ∀ i, HasWeakPartialDeriv i (p i) u O)
    (heq : WeakEquation O (matrixFlux A p) (fun x => c x * u x)) :
    ∀ k, MemWkpLocally k u O := by
  intro k
  induction k with
  | zero => exact locally_of_memWkp hO hu
  | succ k ih =>
      exact (memWkpLocally_add_two_of_weakEquation k hO hA hpos hu hp hpartial
        (ih.smooth_mul hc) heq).mono_order (by omega)

end Poincare.Analysis.Elliptic.Iteration
