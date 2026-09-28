import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusSeamReplacementEnergy
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusSeamGreenTransport












set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "v" => m64AnnulusSeamTranslation



theorem M64ObservedWeakAnnulus.seam_local_energy_le_of_matching_flux
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q) (hei : IsEmbedding e)
    {C : ℝ} (hb : ∀ q, ‖Q q‖ ≤ C)
    (hmin : ∀ B : M64ObservedWeakAnnulus (n := n) e c0 c1, A.energy Q ≤ B.energy Q)
    {K : Set LoopPlane} (hK : IsCompact K) (hKO : K ⊆ m64AnnulusSeamDomain)
    (hsep : Disjoint K ((fun p : LoopPlane => p - v) ⁻¹' K))
    (f : LoopPlane → M) (hf : AEStronglyMeasurable f (volume.restrict K))
    (V : Fin 2 → LoopPlane → E) (hV : ∀ i, MemLp (V i) 2 (volume.restrict K))
    (hfl : MemLp (e ∘ f) 2 (volume.restrict K))
    (ht : ∀ i, ∀ᵐ p ∂volume.restrict K,
      V i p ∈ range (mfderiv (𝓡 n) (𝓡 m) e (f p)))
    (hgreen : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi → ∀ i : Fin 2,
      (∫ p in K, phi p • V i p) +
        (∫ p in K, fderiv ℝ phi p (EuclideanSpace.single i 1) • e (f p)) =
      (∫ p in K, phi p • m64AnnulusSeamExtend (A.column i : LoopPlane → E) p) +
        (∫ p in K, fderiv ℝ phi p (EuclideanSpace.single i 1) •
          e (m64AnnulusSeamExtend A.map p))) :
    (∫ p in K,
      (Q (m64AnnulusSeamExtend A.map p)
        (m64AnnulusSeamExtend (A.column 0 : LoopPlane → E) p)
        (m64AnnulusSeamExtend (A.column 0 : LoopPlane → E) p) +
      Q (m64AnnulusSeamExtend A.map p)
        (m64AnnulusSeamExtend (A.column 1 : LoopPlane → E) p)
        (m64AnnulusSeamExtend (A.column 1 : LoopPlane → E) p)) / 2) ≤
      ∫ p in K, (Q (f p) (V 0 p) (V 0 p) + Q (f p) (V 1 p) (V 1 p)) / 2 := by
  have hu0 := A.seam_extension_memLp.1.mono_measure (Measure.restrict_mono hKO le_rfl)
  have hW0 (i : Fin 2) :=
    (A.seam_extension_memLp.2 i).mono_measure (Measure.restrict_mono hKO le_rfl)
  obtain ⟨B, hmap, hcol⟩ := A.seam_replace hK.measurableSet hKO hsep f V hfl hV ht
    (fun phi hp i htest => m64MatchingGreen_seam_pullback hK hKO
      (e ∘ m64AnnulusSeamExtend A.map) (e ∘ f)
      (m64AnnulusSeamExtend (A.column i : LoopPlane → E)) (V i)
      hu0 hfl (hW0 i) (hV i) (fun psi hpsi => hgreen psi hpsi i) hp htest)
  have hE := m64WeakAnnulusSeamReplacement_energy Q hQ hei hb A B hK.measurableSet hKO hsep
    f hf V hV hmap hcol
  have hm := hmin B
  linarith

end PoincareConjecture
