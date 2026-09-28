import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusSeamGeometry
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakReplacementIntegration












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Manifold

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.Weak

local notation "S" => interior m64AnnulusDomain
local notation "O" => m64AnnulusSeamDomain
local notation "v" => m64AnnulusSeamTranslation



theorem m64AnnulusSeam_integral_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : LoopPlane → E} {phi : LoopPlane → ℝ}
    (hf : MemLp f 2 (volume.restrict S))
    (hp : MemLp phi 2 (volume.restrict O)) :
    (∫ p in O, phi p • m64AnnulusSeamExtend f p) =
      ∫ p in S, (phi p + phi (p - v)) • f p := by
  have hpair : IntegrableOn (fun p => phi p • m64AnnulusSeamExtend f p) O volume :=
    m64L2_test_integrable (m64AnnulusSeamExtend_memLp hf) hp
  have hr := hpair.mono_set m64AnnulusSeam_rect_subset
  have hl := m64AnnulusSeam_negative_translation_measurePreserving.integrable_comp_of_integrable
    (hpair.mono_set m64AnnulusSeam_left_subset)
  change IntegrableOn (fun p => phi (p - v) • m64AnnulusSeamExtend f (p - v)) S volume at hl
  rw [m64AnnulusSeam_integral _ hpair, ← integral_add hr hl]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with p hpS
  rw [m64AnnulusSeamExtend_right f hpS, m64AnnulusSeamExtend_sub f hpS, add_smul]



theorem m64AnnulusSeam_test_memLp {phi : LoopPlane → ℝ}
    (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi) (i : Fin 2) :
    MemLp phi 2 (volume.restrict O) ∧
      MemLp (fun p => fderiv ℝ phi p (EuclideanSpace.single i 1)) 2 (volume.restrict O) := by
  constructor
  · exact (hp.continuous.memLp_of_hasCompactSupport (μ := volume) (p := 2) hc).mono_measure
      (Measure.restrict_le_self (s := O))
  · exact (((hp.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (μ := volume) (p := 2) (hc.fderiv_apply ℝ (EuclideanSpace.single i 1))).mono_measure
        (Measure.restrict_le_self (s := O))

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)



theorem M64ObservedWeakAnnulus.seam_extension_memLp
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1) :
    MemLp (e ∘ m64AnnulusSeamExtend A.map) 2 (volume.restrict O) ∧
      ∀ i, MemLp (m64AnnulusSeamExtend (A.column i : LoopPlane → E)) 2 (volume.restrict O) := by
  constructor
  · rw [m64AnnulusSeamExtend_comp]
    exact m64AnnulusSeamExtend_memLp A.observed_memLp
  · intro i
    exact m64AnnulusSeamExtend_memLp (Lp.memLp (A.column i))



theorem M64ObservedWeakAnnulus.seam_extension_tangent
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1) (i : Fin 2) :
    ∀ᵐ p ∂volume.restrict O,
      m64AnnulusSeamExtend (A.column i : LoopPlane → E) p ∈
        range (mfderiv (𝓡 n) (𝓡 m) e (m64AnnulusSeamExtend A.map p)) := by
  rw [Measure.restrict_congr_set m64AnnulusSeamDomain_ae_union]
  apply (ae_restrict_union_iff _ _ _).mpr
  constructor
  · filter_upwards [A.tangent i, ae_restrict_mem isOpen_interior.measurableSet] with p hp hpS
    rw [m64AnnulusSeamExtend_right _ hpS, m64AnnulusSeamExtend_right _ hpS]
    exact hp
  · have h := m64AnnulusSeam_translation_measurePreserving.quasiMeasurePreserving.ae (A.tangent i)
    filter_upwards [h, ae_restrict_mem m64AnnulusSeamLeft_isOpen.measurableSet] with p hp hpS
    rw [m64AnnulusSeamExtend_left _ hpS, m64AnnulusSeamExtend_left _ hpS]
    exact hp



theorem M64ObservedWeakAnnulus.seam_extension_green
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    {phi : LoopPlane → ℝ} (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi)
    (hs : tsupport phi ⊆ O) (i : Fin 2) :
    (∫ p in O, phi p • m64AnnulusSeamExtend (A.column i : LoopPlane → E) p) +
      (∫ p in O, fderiv ℝ phi p (EuclideanSpace.single i 1) •
        e (m64AnnulusSeamExtend A.map p)) = 0 := by
  have hphi := m64AnnulusSeam_test_memLp hp hc i
  have hcomp (p : LoopPlane) : e (m64AnnulusSeamExtend A.map p) =
      m64AnnulusSeamExtend (e ∘ A.map) p :=
    congrFun (m64AnnulusSeamExtend_comp A.map e) p
  simp_rw [hcomp]
  rw [m64AnnulusSeam_integral_smul (Lp.memLp (A.column i)) hphi.1,
    m64AnnulusSeam_integral_smul A.observed_memLp hphi.2]
  exact A.seam_folded_green hp hs i



theorem M64ObservedWeakAnnulus.seam_extension_weak_partial
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1) (i : Fin 2) (b : Fin m) :
    HasWeakPartialDeriv i
      (fun p => m64AnnulusSeamExtend (A.column i : LoopPlane → E) p b)
      (fun p => e (m64AnnulusSeamExtend A.map p) b) O := by
  intro phi hp hc hs
  have hphi := m64AnnulusSeam_test_memLp hp hc i
  let L := EuclideanSpace.proj (𝕜 := ℝ) b
  have hproj (f : LoopPlane → E) (hf : MemLp f 2 (volume.restrict O))
      (psi : LoopPlane → ℝ) (hpsi : MemLp psi 2 (volume.restrict O)) :
      L (∫ p in O, psi p • f p) = ∫ p in O, psi p * f p b := by
    simpa only [map_smul, smul_eq_mul, L, EuclideanSpace.coe_proj] using
      (L.integral_comp_comm (m64L2_test_integrable hf hpsi)).symm
  have h := congrArg L (A.seam_extension_green hp hc hs i)
  simp only [map_add, map_zero] at h
  have hvalue : MemLp (fun p => e (m64AnnulusSeamExtend A.map p)) 2 (volume.restrict O) :=
    A.seam_extension_memLp.1
  rw [hproj _ (A.seam_extension_memLp.2 i) _ hphi.1,
    hproj _ hvalue _ hphi.2] at h
  simp only [mul_comm] at h ⊢
  linarith



theorem M64ObservedWeakAnnulus.seam_extension_energy
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q)
    (hei : Topology.IsEmbedding e) {C : ℝ} (hb : ∀ q, ‖Q q‖ ≤ C) :
    (∫ p in O,
      (Q (m64AnnulusSeamExtend A.map p)
        (m64AnnulusSeamExtend (A.column 0 : LoopPlane → E) p)
        (m64AnnulusSeamExtend (A.column 0 : LoopPlane → E) p) +
      Q (m64AnnulusSeamExtend A.map p)
        (m64AnnulusSeamExtend (A.column 1 : LoopPlane → E) p)
        (m64AnnulusSeamExtend (A.column 1 : LoopPlane → E) p)) / 2) = 2 * A.energy Q := by
  have heq : (fun p =>
      (Q (m64AnnulusSeamExtend A.map p)
        (m64AnnulusSeamExtend (A.column 0 : LoopPlane → E) p)
        (m64AnnulusSeamExtend (A.column 0 : LoopPlane → E) p) +
      Q (m64AnnulusSeamExtend A.map p)
        (m64AnnulusSeamExtend (A.column 1 : LoopPlane → E) p)
        (m64AnnulusSeamExtend (A.column 1 : LoopPlane → E) p)) / 2) =
      m64AnnulusSeamExtend (fun p =>
        (Q (A.map p) (A.column 0 p) (A.column 0 p) +
          Q (A.map p) (A.column 1 p) (A.column 1 p)) / 2) := by
    funext p
    simp only [m64AnnulusSeamExtend]
    split_ifs <;> rfl
  rw [heq, m64AnnulusSeamExtend_integral _ (A.energy_integrable Q hQ hei hb)]
  simp only [nsmul_eq_mul, Nat.cast_ofNat, M64ObservedWeakAnnulus.energy]

end PoincareConjecture
