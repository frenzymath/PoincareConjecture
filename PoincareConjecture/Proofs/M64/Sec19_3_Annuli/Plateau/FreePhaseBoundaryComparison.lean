import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakAnnulusBoundaryReplacement
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreePhaseBoundaryReplacement
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryReplacementEnergy

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology ContDiff Manifold

namespace PoincareConjecture.M64FreeWeakPhaseAnnulus

open Proofs.M58

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)}
  {R : EuclideanSpace ℝ (Fin m) →L[ℝ] LoopPlane} {c0 c1 : ℝ → M}
  {H0 H1 : ℝ ≃o ℝ} {k D : ℝ}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S
local notation "I" => Icc (0 : ℝ) curvePeriod

theorem local_energy_le_of_boundary_flux
    (A : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k D)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q) (hei : IsEmbedding e)
    {bound : ℝ} (hb : ∀ q, ‖Q q‖ ≤ bound) (hpos : ∀ q v, 0 ≤ Q q v v)
    {r : ℝ} (hr : 0 < r)
    (hminimum : ∀ C : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k D,
      A.annulus.weightedEnergy Q r ≤ C.annulus.weightedEnergy Q r)
    {sigma0 sigma1 : ℝ → ℝ} (hm0 : Monotone sigma0) (hm1 : Monotone sigma1)
    (hp0 : ∀ x, sigma0 (x + curvePeriod) = sigma0 x + curvePeriod)
    (hp1 : ∀ x, sigma1 (x + curvePeriod) = sigma1 x + curvePeriod)
    (hn0 : sigma0 0 ∈ I) (hn1 : sigma1 0 ∈ I)
    {K : Set LoopPlane} [DecidablePred (· ∈ K)] (hK : MeasurableSet K) (hKS : K ⊆ S)
    (f : LoopPlane → M) (V : Fin 2 → LoopPlane → E)
    (hf : MemLp (e ∘ f) 2 (volume.restrict K))
    (hV : ∀ i, MemLp (V i) 2 (volume.restrict K))
    (ht : ∀ i, ∀ᵐ p ∂volume.restrict K,
      V i p ∈ range (mfderiv (𝓡 n) (𝓡 m) e (f p)))
    (hgreen : ∀ (phi : LoopPlane → ℝ), ContDiff ℝ 1 phi → ∀ i : Fin 2,
      (∫ p in K, phi p • V i p) +
        (∫ p in K, fderiv ℝ phi p (EuclideanSpace.single i 1) • e (f p)) =
      (∫ p in K, phi p • A.annulus.column i p) +
        (∫ p in K, fderiv ℝ phi p (EuclideanSpace.single i 1) • e (A.annulus.map p)) +
      if i = 1 then
        (∫ x in I, phi (annulusPoint x 1) • e (c1 (sigma1 x)) -
          phi (annulusPoint x 0) • e (c0 (sigma0 x))) -
        (∫ x in I, phi (annulusPoint x 1) • e (c1 (A.label1 x)) -
          phi (annulusPoint x 0) • e (c0 (A.label0 x))) else 0)
    {u : LoopPlane → ℝ} {W : Fin 2 → LoopPlane → ℝ}
    (hu : MemLp u 2 (volume.restrict K))
    (hW : ∀ i, MemLp (W i) 2 (volume.restrict K))
    (hphase : ∀ (phi : LoopPlane → ℝ), ContDiff ℝ 1 phi → ∀ i : Fin 2,
      (∫ p in K, phi p * W i p) +
        (∫ p in K, fderiv ℝ phi p (EuclideanSpace.single i 1) * u p) =
      (∫ p in K, phi p * A.phaseColumn i p) +
        (∫ p in K, fderiv ℝ phi p (EuclideanSpace.single i 1) * A.phase p) +
      if i = 1 then
        (∫ x in I, phi (annulusPoint x 1) * (H1 (sigma1 x) + A.offset) -
          phi (annulusPoint x 0) * H0 (sigma0 x)) -
        (∫ x in I, phi (annulusPoint x 1) * (H1 (A.label1 x) + A.offset) -
          phi (annulusPoint x 0) * H0 (A.label0 x)) else 0)
    (hobs : (fun p => R (e (K.piecewise f A.annulus.map p))) =ᵐ[mu]
      fun p => angularPoint (k * K.piecewise u A.phase p)) :
    (∫ p in K, (Q (A.annulus.map p) (A.annulus.column 0 p) (A.annulus.column 0 p) +
      Q (A.annulus.map p) (A.annulus.column 1 p) (A.annulus.column 1 p)) / 2) ≤
      (max r r⁻¹) ^ 2 *
        ∫ p in K, (Q (f p) (V 0 p) (V 0 p) + Q (f p) (V 1 p) (V 1 p)) / 2 := by
  obtain ⟨B, hBmap, hBcol⟩ := A.annulus.replace_boundary
    (d0 := c0 ∘ sigma0) (d1 := c1 ∘ sigma1) hK hKS f V hf hV ht hgreen
  have hBobs : (fun p => R (e (B.map p))) =ᵐ[mu]
      fun p => angularPoint (k * K.piecewise u A.phase p) := by
    simpa only [hBmap] using hobs
  obtain ⟨C, _hc0, _hc1, hCmap, hCcol, _hCu, _hCW, _hCoffset⟩ :=
    A.exists_phase_boundary_replacement hm0 hm1 hp0 hp1 hn0 hn1 B
      hK hKS hu hW hphase hBobs
  have hfm : AEStronglyMeasurable f (volume.restrict K) := by
    let : TopologicalSpace.PseudoMetrizableSpace M := hei.isInducing.pseudoMetrizableSpace
    exact hei.aestronglyMeasurable_comp_iff.mp hf.aestronglyMeasurable
  apply boundary_local_energy_le R A C Q hQ hei hb hpos hr (hminimum C)
    hK hKS f hfm V hV (hCmap.trans hBmap)
  intro i
  simpa only [hCcol i] using hBcol i

end PoincareConjecture.M64FreeWeakPhaseAnnulus
