import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryFaceTests
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerCompactWeakChain













noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal ContDiff
open Poincare.Analysis.Sobolev.Weak

namespace PoincareConjecture





theorem m64NaturalGrowth_compact_coefficient_face_test
    {n : ℕ} (dirichlet : Prop) {O S : Set LoopPlane} (hO : IsOpen O)
    {F : Fin 2 → LoopPlane → ℝ} {b : LoopPlane → ℝ}
    (hF : ∀ i, MemLp (F i) 2 volume) (hb : Integrable b)
    (hFzero : ∀ i p, p 1 ≤ 0 → F i p = 0)
    (hbzero : ∀ p, p 1 ≤ 0 → b p = 0)
    {u : LoopPlane → EuclideanSpace ℝ (Fin n)} (hu : Continuous u)
    {V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin n)}
    (hV : ∀ i, MemLp (V i) 2 volume)
    (hw : ∀ i j, HasWeakPartialDeriv i (fun p => V i p j) (fun p => u p j) univ)
    {U K : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) (hmap : MapsTo u S K)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiffOn ℝ 1 f U)
    {phi : LoopPlane → ℝ} (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi)
    (hs : tsupport phi ⊆ O) (hsS : tsupport phi ⊆ S)
    (hz : dirichlet → ∀ p : LoopPlane, p 1 = 0 → phi p * f (u p) = 0)
    (heq : ∀ psi : LoopPlane → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi →
      tsupport psi ⊆ O → (dirichlet → ∀ p : LoopPlane, p 1 = 0 → psi p = 0) →
      (∫ p, ∑ i : Fin 2, F i p * fderiv ℝ psi p (EuclideanSpace.single i 1)) =
        ∫ p, b p * psi p) :
    (∫ p, ∑ i : Fin 2, F i p * (phi p * fderiv ℝ f (u p) (V i p) +
        fderiv ℝ phi p (EuclideanSpace.single i 1) * f (u p))) =
      ∫ p, b p * (phi p * f (u p)) := by
  obtain ⟨g, C, hg, hC, hdg, he⟩ := M60.suC1_coefficient_compact_extension hU hK hKU hf
  have hv (p : LoopPlane) : phi p * g (u p) = phi p * f (u p) := by
    by_cases hpt : p ∈ tsupport phi
    · rw [(he _ (hmap (hsS hpt))).self_of_nhds]
    · rw [image_eq_zero_of_notMem_tsupport hpt, zero_mul, zero_mul]
  have hder (p : LoopPlane) (i : Fin 2) :
      phi p * fderiv ℝ g (u p) (V i p) +
        fderiv ℝ phi p (EuclideanSpace.single i 1) * g (u p) =
      phi p * fderiv ℝ f (u p) (V i p) +
        fderiv ℝ phi p (EuclideanSpace.single i 1) * f (u p) := by
    by_cases hpt : p ∈ tsupport phi
    · rw [(he _ (hmap (hsS hpt))).self_of_nhds, (he _ (hmap (hsS hpt))).fderiv_eq]
    · rw [image_eq_zero_of_notMem_tsupport hpt, fderiv_of_notMem_tsupport ℝ hpt]
      simp
  have ht := m64NaturalGrowth_coefficient_face_test dirichlet hO hF hb hFzero hbzero
    hu hV hw hg hC hdg hp hc hs (fun hd p hp0 => by rw [hv]; exact hz hd p hp0) heq
  simpa only [hder, hv] using ht

end PoincareConjecture
