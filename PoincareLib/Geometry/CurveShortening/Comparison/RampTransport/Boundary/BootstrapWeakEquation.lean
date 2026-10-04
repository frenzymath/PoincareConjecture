import PoincareLib.Geometry.CurveShortening.Comparison.RampTransport.Boundary.BootstrapClassicalJets

/-!
# The weak equation of the actual smooth interior representative

The literal scalar Laplacian is integrated against compact interior tests.
Its L2 derivative fields are the same chosen derivatives used by the
Dirichlet and Neumann boundary gains.
Source: MT Lemma 19.31, pp. 464-466, finite boundary-bootstrap derivation,
Section 4.
-/

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff ENNReal

namespace PoincareMT.M64.RampTransport

open Poincare.Analysis.Sobolev
open Weak Euclidean

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

/-- The original ordinary Laplacian equation yields the actual weak flat principal equation,
with chosen weak derivatives of the same map. Source: MT Lemma 19.31 finite boundary
bootstrap, derivation Section 4. Source: Morgan--Tian Lemma 19.31, printed pp. 464-466;
project derivation
`proof-work/tasks/M64/derivations/2026-09-27-smooth-boundary-bootstrap-plan.md`. -/
theorem weak_flat_equation_of_classical
    {O : Set Plane} (hO : IsOpen O) {u f : Plane → ℝ}
    (hs : ContDiffOn ℝ ∞ u O) (hu : MemWkp 2 2 u O)
    (heq : ∀ z ∈ O, -(∑ i : Fin 2,
      boundaryClassicalPartial i (boundaryClassicalPartial i u) z) = f z) :
    ∀ phi : Plane → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
      tsupport phi ⊆ O →
      (∫ z in O, ∑ i, chosenWeakPartial' 2 i u O z *
        fderiv ℝ phi z (EuclideanSpace.single i 1)) = ∫ z in O, f z * phi z := by
  intro phi hphi hc hsupp
  let P := fun i => boundaryClassicalPartial i u
  let Q := fun i => boundaryClassicalPartial i (P i)
  have hPs (i : Fin 2) : ContDiffOn ℝ ∞ (P i) O :=
    (hs.fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const
  have hP (i : Fin 2) : MemWkp 1 2 (P i) O :=
    boundaryClassicalPartial_memWkp 1 hO (hs.of_le (by simp)) hu i
  have hQ (i : Fin 2) : MemLp (Q i) 2 (volume.restrict O) :=
    boundaryClassicalPartial_memWkp 0 hO ((hPs i).of_le (by simp)) (hP i) i
  have hphi2 : MemLp phi 2 (volume.restrict O) :=
    (hphi.continuous.memLp_of_hasCompactSupport hc).restrict O
  have hdphi2 (i : Fin 2) : MemLp
      (fun z => fderiv ℝ phi z (EuclideanSpace.single i 1)) 2 (volume.restrict O) :=
    (((hphi.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hc.fderiv_apply ℝ _)).restrict O
  have hPI (i : Fin 2) : Integrable
      (fun z => P i z * fderiv ℝ phi z (EuclideanSpace.single i 1)) (volume.restrict O) :=
    (hP i).memLp.integrable_mul (hdphi2 i)
  have hQI (i : Fin 2) : Integrable (fun z => Q i z * phi z) (volume.restrict O) :=
    (hQ i).integrable_mul hphi2
  have hweak (i : Fin 2) :
      (∫ z in O, P i z * fderiv ℝ phi z (EuclideanSpace.single i 1)) =
        -(∫ z in O, Q i z * phi z) :=
    hasWeakPartial_boundaryClassicalPartial hO ((hPs i).of_le (by simp)) i
      phi hphi hc hsupp
  have hchosen (i : Fin 2) : chosenWeakPartial' 2 i u O =ᵐ[volume.restrict O] P i :=
    m64WeakPartial_eq_fderiv_of_contDiffOn hO (hs.of_le (by simp))
      (chosenWeakPartial'_memLp_of_mem hu.memW1p i)
      (chosenWeakPartial'_isWeakPartial_of_mem hu.memW1p i)
  have hleft : (∫ z in O, ∑ i, chosenWeakPartial' 2 i u O z *
      fderiv ℝ phi z (EuclideanSpace.single i 1)) =
      -(∫ z in O, Q 0 z * phi z) - ∫ z in O, Q 1 z * phi z := by
    have hae : (fun z => ∑ i, chosenWeakPartial' 2 i u O z *
        fderiv ℝ phi z (EuclideanSpace.single i 1)) =ᵐ[volume.restrict O]
        (fun z => P 0 z * fderiv ℝ phi z (EuclideanSpace.single 0 1) +
          P 1 z * fderiv ℝ phi z (EuclideanSpace.single 1 1)) := by
      filter_upwards [hchosen 0, hchosen 1] with z h0 h1
      simp only [Fin.sum_univ_two, h0, h1]
    rw [integral_congr_ae hae, integral_add (hPI 0) (hPI 1), hweak 0, hweak 1]
    ring
  rw [hleft]
  have hright : (∫ z in O, f z * phi z) =
      -(∫ z in O, Q 0 z * phi z) - ∫ z in O, Q 1 z * phi z := by
    have hae : (fun z => f z * phi z) =ᵐ[volume.restrict O]
        (fun z => -(Q 0 z * phi z) - Q 1 z * phi z) := by
      filter_upwards [ae_restrict_mem hO.measurableSet] with z hz
      rw [← heq z hz, Fin.sum_univ_two]
      change -(Q 0 z + Q 1 z) * phi z = _
      ring
    have hneg : Integrable (fun z => -(Q 0 z * phi z)) (volume.restrict O) := (hQI 0).neg
    rw [integral_congr_ae hae, integral_sub hneg (hQI 1), integral_neg]
  exact hright.symm

/-- Each component of the actual vector Laplacian equation has the chosen-partial weak
equation required by the finite boundary gains. Source: MT Lemma 19.31 finite boundary
bootstrap, derivation Section 4. Source: Morgan--Tian Lemma 19.31, printed pp. 464-466;
project derivation
`proof-work/tasks/M64/derivations/2026-09-27-smooth-boundary-bootstrap-plan.md`. -/
theorem weak_coordinate_flat_equation_of_classical {n : ℕ}
    {O : Set Plane} (hO : IsOpen O) {u : Plane → EuclideanSpace ℝ (Fin n)}
    {f : Plane → ℝ} (hs : ContDiffOn ℝ ∞ u O) (j : Fin n)
    (hu : MemWkp 2 2 (fun z => u z j) O)
    (heq : ∀ z ∈ O, -(∑ i : Fin 2, (fderiv ℝ (fderiv ℝ u) z
      (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) j) = f z) :
    ∀ phi : Plane → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
      tsupport phi ⊆ O →
      (∫ z in O, ∑ i, chosenWeakPartial' 2 i (fun p => u p j) O z *
        fderiv ℝ phi z (EuclideanSpace.single i 1)) = ∫ z in O, f z * phi z := by
  apply weak_flat_equation_of_classical hO
    ((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp_contDiffOn hs) hu
  intro z hz
  rw [← heq z hz]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact boundaryClassicalSecond_coordinate (hs.contDiffAt (hO.mem_nhds hz)) i i j

end PoincareMT.M64.RampTransport
