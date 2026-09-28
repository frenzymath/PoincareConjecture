import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRadialWeakExtension












set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.Weak

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain
local notation "O" => m64AnnulusLowerDomain
local notation "v" => m64AnnulusRadialTranslation



theorem m64Observed_classical_column_tangent
    (he : ContMDiff (𝓡 n) (𝓡 m) 1 e) {F : LoopPlane → M}
    (hF : ContMDiff (𝓡 2) (𝓡 n) 1 F) (p : LoopPlane) (i : Fin 2) :
    fderiv ℝ (e ∘ F) p (EuclideanSpace.single i 1) ∈
      range (mfderiv (𝓡 n) (𝓡 m) e (F p)) := by
  refine ⟨mfderiv (𝓡 2) (𝓡 n) F p (EuclideanSpace.single i 1), ?_⟩
  have hc := mfderiv_comp p (he.mdifferentiable (by simp) _) (hF.mdifferentiable (by simp) _)
  have hd := congrArg (fun L => L (EuclideanSpace.single i 1)) hc
  rw [mfderiv_eq_fderiv] at hd
  exact hd.symm



theorem M64ObservedWeakAnnulus.lower_extension_tangent
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (he : ContMDiff (𝓡 n) (𝓡 m) 1 e) (hc0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 c0)
    (i : Fin 2) : ∀ᵐ p ∂volume.restrict O,
      A.lowerExtensionColumn i p ∈ range (mfderiv (𝓡 n) (𝓡 m) e (A.lowerExtensionMap p)) := by
  let cb : LoopPlane → M := fun p => c0 (p 0)
  have hcb : ContMDiff (𝓡 2) (𝓡 n) 1 cb :=
    hc0.comp (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff.contMDiff
  have ht (p : LoopPlane) := m64Observed_classical_column_tangent he hcb p i
  have hlocal := (ae_restrict_iff' isOpen_interior.measurableSet).mp (A.tangent i)
  filter_upwards [ae_restrict_of_ae m64AnnulusLowerDomain_ae_union,
    ae_restrict_mem m64AnnulusLowerDomain_isOpen.measurableSet, ae_restrict_of_ae hlocal]
    with p hp hpO hlocal
  rcases hp.mp hpO with hpS | hpL
  · have hmap : A.lowerExtensionMap p = A.map p := m64AnnulusLowerExtend_right _ _ hpS
    rw [hmap]
    have hcol : A.lowerExtensionColumn i p = A.column i p :=
      m64AnnulusLowerExtend_right _ _ hpS
    rw [hcol]
    exact hlocal hpS
  · have hmap : A.lowerExtensionMap p = cb (v + p) :=
      m64AnnulusLowerExtend_left _ _ hpL
    rw [hmap]
    have hcol : A.lowerExtensionColumn i p =
        fderiv ℝ (e ∘ cb) (v + p) (EuclideanSpace.single i 1) :=
      m64AnnulusLowerExtend_left _ _ hpL
    rw [hcol]
    exact ht (v + p)



theorem M64ObservedWeakAnnulus.lower_extension_data
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (he : ContMDiff (𝓡 n) (𝓡 m) 1 e) (hc0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 c0) :
    MemLp (e ∘ A.lowerExtensionMap) 2 (volume.restrict O) ∧
      (∀ i, MemLp (A.lowerExtensionColumn i) 2 (volume.restrict O)) ∧
      (∀ i b, HasWeakPartialDeriv i (fun p => A.lowerExtensionColumn i p b)
        (fun p => e (A.lowerExtensionMap p) b) O) ∧
      ∀ i, ∀ᵐ p ∂volume.restrict O,
        A.lowerExtensionColumn i p ∈ range (mfderiv (𝓡 n) (𝓡 m) e (A.lowerExtensionMap p)) := by
  have hobs : ContDiff ℝ 1 (e ∘ c0) := contMDiff_iff_contDiff.mp (he.comp hc0)
  exact ⟨(A.lower_extension_memLp hobs).1, (A.lower_extension_memLp hobs).2,
    A.lower_extension_weak_partial hobs, A.lower_extension_tangent he hc0⟩

end PoincareConjecture
