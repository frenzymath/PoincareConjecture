import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusSeamDiskReplacement
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakReplacementEnergy













set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.Weak

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S
local notation "v" => m64AnnulusSeamTranslation



theorem m64WeakAnnulusSeamReplacement_energy
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q) (hei : IsEmbedding e)
    {C : ℝ} (hb : ∀ q, ‖Q q‖ ≤ C)
    (A B : M64ObservedWeakAnnulus (n := n) e c0 c1)
    {K : Set LoopPlane} (hK : MeasurableSet K) (hKO : K ⊆ m64AnnulusSeamDomain)
    (hsep : Disjoint K ((fun p : LoopPlane => p - v) ⁻¹' K))
    (f : LoopPlane → M) (hf : AEStronglyMeasurable f (volume.restrict K))
    (V : Fin 2 → LoopPlane → E) (hV : ∀ i, MemLp (V i) 2 (volume.restrict K))
    (hmap : B.map = m64AnnulusSeamPatch K f A.map)
    (hcol : ∀ i, (B.column i : LoopPlane → E) =ᵐ[mu]
      m64AnnulusSeamPatch K (V i) (A.column i)) :
    B.energy Q = A.energy Q +
      (∫ p in K, (Q (f p) (V 0 p) (V 0 p) + Q (f p) (V 1 p) (V 1 p)) / 2) -
      ∫ p in K,
        (Q (m64AnnulusSeamExtend A.map p)
          (m64AnnulusSeamExtend (A.column 0 : LoopPlane → E) p)
          (m64AnnulusSeamExtend (A.column 0 : LoopPlane → E) p) +
        Q (m64AnnulusSeamExtend A.map p)
          (m64AnnulusSeamExtend (A.column 1 : LoopPlane → E) p)
          (m64AnnulusSeamExtend (A.column 1 : LoopPlane → E) p)) / 2 := by
  classical
  let old := fun p => (Q (A.map p) (A.column 0 p) (A.column 0 p) +
    Q (A.map p) (A.column 1 p) (A.column 1 p)) / 2
  let new := fun p => (Q (f p) (V 0 p) (V 0 p) + Q (f p) (V 1 p) (V 1 p)) / 2
  have heq : (fun p => (Q (B.map p) (B.column 0 p) (B.column 0 p) +
      Q (B.map p) (B.column 1 p) (B.column 1 p)) / 2) =ᵐ[mu]
      m64AnnulusSeamPatch K new old := by
    filter_upwards [hcol 0, hcol 1] with p h0 h1
    rw [h0, h1, hmap]
    simp only [m64AnnulusSeamPatch]
    split_ifs <;> rfl
  have hi : IntegrableOn new K volume := m64Observed_energyDensity_integrable Q hQ hb f hf V hV
  have ho : IntegrableOn old S volume := A.energy_integrable Q hQ hei hb
  have hoK : IntegrableOn (m64AnnulusSeamExtend old) K volume :=
    memLp_one_iff_integrable.mp ((m64AnnulusSeamExtend_memLp
      (memLp_one_iff_integrable.mpr ho)).mono_measure (Measure.restrict_mono hKO le_rfl))
  have hext (p : LoopPlane) : m64AnnulusSeamExtend old p =
      (Q (m64AnnulusSeamExtend A.map p)
        (m64AnnulusSeamExtend (A.column 0 : LoopPlane → E) p)
        (m64AnnulusSeamExtend (A.column 0 : LoopPlane → E) p) +
      Q (m64AnnulusSeamExtend A.map p)
        (m64AnnulusSeamExtend (A.column 1 : LoopPlane → E) p)
        (m64AnnulusSeamExtend (A.column 1 : LoopPlane → E) p)) / 2 := by
    simp only [m64AnnulusSeamExtend]
    split_ifs <;> rfl
  unfold M64ObservedWeakAnnulus.energy
  rw [integral_congr_ae heq, m64AnnulusSeamPatch_integral hK hKO hsep hi ho,
    integral_sub hi hoK]
  simp only [hext, new, old]
  ring



theorem M64ObservedWeakAnnulus.exists_seam_local_comparison_of_outer_agreement
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q) (hei : IsEmbedding e)
    {C : ℝ} (hb : ∀ q, ‖Q q‖ ≤ C)
    (hmin : ∀ B : M64ObservedWeakAnnulus (n := n) e c0 c1, A.energy Q ≤ B.energy Q)
    {O : Set LoopPlane} (hO : IsOpen O) (a : LoopPlane)
    {rho : ℝ} (hrho : 0 < rho) (hwidth : 2 * rho < curvePeriod)
    (hKO : Metric.closedBall a rho ⊆ O)
    (hKS : Metric.closedBall a rho ⊆ m64AnnulusSeamDomain)
    (f : LoopPlane → M) (V : Fin 2 → LoopPlane → E)
    (hf : MemLp (e ∘ f) 2 (volume.restrict O))
    (hV : ∀ i, MemLp (V i) 2 (volume.restrict O))
    (hw : ∀ i b, HasWeakPartialDeriv i (fun p => V i p b) (fun p => e (f p) b) O)
    (ht : ∀ i, ∀ᵐ p ∂volume.restrict O,
      V i p ∈ range (mfderiv (𝓡 n) (𝓡 m) e (f p)))
    (hmatch : ∀ p : LoopPlane, rho * Real.exp (-1) ≤ dist p a →
      dist p a ≤ rho → f p = m64AnnulusSeamExtend A.map p) :
    ∃ r : ℝ, 0 < r ∧ rho * Real.exp (-1) ≤ r ∧ r ≤ rho ∧
      (∫ p in Metric.closedBall a r,
        (Q (m64AnnulusSeamExtend A.map p)
          (m64AnnulusSeamExtend (A.column 0 : LoopPlane → E) p)
          (m64AnnulusSeamExtend (A.column 0 : LoopPlane → E) p) +
        Q (m64AnnulusSeamExtend A.map p)
          (m64AnnulusSeamExtend (A.column 1 : LoopPlane → E) p)
          (m64AnnulusSeamExtend (A.column 1 : LoopPlane → E) p)) / 2) ≤
      ∫ p in Metric.closedBall a r,
        (Q (f p) (V 0 p) (V 0 p) + Q (f p) (V 1 p) (V 1 p)) / 2 := by
  obtain ⟨r, hr, hlo, hhi, B, hmap, hcol⟩ :=
    A.exists_seam_replacement_of_outer_agreement hO a hrho hwidth hKO hKS f V hf hV hw ht hmatch
  have hsmallO := (Metric.closedBall_subset_closedBall hhi).trans hKO
  have hsmallS := (Metric.closedBall_subset_closedBall hhi).trans hKS
  let : TopologicalSpace.PseudoMetrizableSpace M := hei.isInducing.pseudoMetrizableSpace
  have hfm : AEStronglyMeasurable f (volume.restrict (Metric.closedBall a r)) :=
    hei.aestronglyMeasurable_comp_iff.mp
      (hf.mono_measure (Measure.restrict_mono hsmallO le_rfl)).aestronglyMeasurable
  have hE := m64WeakAnnulusSeamReplacement_energy Q hQ hei hb A B
    Metric.isClosed_closedBall.measurableSet hsmallS
    (m64AnnulusSeamDisk_disjoint a (r := r) (by linarith)) f hfm V
    (fun i => (hV i).mono_measure (Measure.restrict_mono hsmallO le_rfl)) hmap hcol
  refine ⟨r, hr, hlo, hhi, ?_⟩
  have hm := hmin B
  linarith

end PoincareConjecture
