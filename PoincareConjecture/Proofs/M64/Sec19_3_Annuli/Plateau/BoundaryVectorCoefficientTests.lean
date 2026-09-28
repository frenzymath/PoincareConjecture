import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryCompactCoefficientTests













noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal ContDiff
open Poincare.Analysis.Sobolev.Weak

namespace PoincareConjecture

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

private theorem compact_coefficient_products
    {F : Fin 2 → LoopPlane → ℝ} {b : LoopPlane → ℝ}
    (hF : ∀ i, MemLp (F i) 2 volume) (hb : Integrable b)
    {u : LoopPlane → E} (hu : Continuous u)
    {V : Fin 2 → LoopPlane → E} (hV : ∀ i, MemLp (V i) 2 volume)
    (hw : ∀ i j, HasWeakPartialDeriv i (fun p => V i p j) (fun p => u p j) univ)
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {A : Set LoopPlane} (hmap : MapsTo u A K)
    {f : E → ℝ} (hf : ContDiffOn ℝ 1 f U)
    {phi : LoopPlane → ℝ} (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi)
    (hs : tsupport phi ⊆ A) :
    (∀ i, Integrable (fun p => F i p *
      (phi p * fderiv ℝ f (u p) (V i p)))) ∧
    (∀ i, Integrable (fun p => F i p *
      (fderiv ℝ phi p (EuclideanSpace.single i 1) * f (u p)))) ∧
    Integrable (fun p => b p * (phi p * f (u p))) := by
  obtain ⟨g, C, hg, hC, hdg, he⟩ :=
    M60.suC1_coefficient_compact_extension hU hK hKU hf
  have hval (p : LoopPlane) : phi p * g (u p) = phi p * f (u p) := by
    by_cases hpt : p ∈ tsupport phi
    · rw [(he _ (hmap (hs hpt))).self_of_nhds]
    · rw [image_eq_zero_of_notMem_tsupport hpt, zero_mul, zero_mul]
  have hfst (p : LoopPlane) (i : Fin 2) :
      phi p * fderiv ℝ g (u p) (V i p) =
        phi p * fderiv ℝ f (u p) (V i p) := by
    by_cases hpt : p ∈ tsupport phi
    · rw [(he _ (hmap (hs hpt))).fderiv_eq]
    · rw [image_eq_zero_of_notMem_tsupport hpt, zero_mul, zero_mul]
  have hsnd (p : LoopPlane) (i : Fin 2) :
      fderiv ℝ phi p (EuclideanSpace.single i 1) * g (u p) =
        fderiv ℝ phi p (EuclideanSpace.single i 1) * f (u p) := by
    by_cases hpt : p ∈ tsupport phi
    · rw [(he _ (hmap (hs hpt))).self_of_nhds]
    · rw [fderiv_of_notMem_tsupport ℝ hpt]
      simp
  have hsecond (i : Fin 2) : MemLp (fun p =>
      fderiv ℝ phi p (EuclideanSpace.single i 1) * g (u p)) 2 volume :=
    (((hp.continuous_fderiv (by simp)).clm_apply continuous_const).mul
      (hg.continuous.comp hu)).memLp_of_hasCompactSupport
        ((hc.fderiv_apply ℝ _).mul_right)
  have hfirst (i : Fin 2) : MemLp
      (fun p => phi p * fderiv ℝ g (u p) (V i p)) 2 volume := by
    have h := ((m64CompactCoefficientTest_weak_derivatives hu hV hw
      hg hC hdg hp hc i).1).sub (hsecond i)
    change MemLp (fun p => (phi p * fderiv ℝ g (u p) (V i p) +
      fderiv ℝ phi p (EuclideanSpace.single i 1) * g (u p)) -
        fderiv ℝ phi p (EuclideanSpace.single i 1) * g (u p)) 2 volume at h
    simpa only [Pi.sub_apply, add_sub_cancel_right] using h
  refine ⟨?_, ?_, ?_⟩
  · intro i
    simpa only [Pi.mul_apply, hfst] using! (hF i).integrable_mul (hfirst i)
  · intro i
    simpa only [Pi.mul_apply, hsnd] using! (hF i).integrable_mul (hsecond i)
  · have h := hb.locallyIntegrable.integrable_smul_right_of_hasCompactSupport
      (hp.continuous.mul (hg.continuous.comp hu)) hc.mul_right
    simpa only [smul_eq_mul, Pi.mul_apply, Function.comp_apply, hval] using h

set_option maxHeartbeats 800000 in





theorem m64NaturalGrowth_compact_vector_face_test
    (dirichlet : Fin n → Prop) {O A : Set LoopPlane} (hO : IsOpen O)
    {F : Fin n → Fin 2 → LoopPlane → ℝ} {b : Fin n → LoopPlane → ℝ}
    (hF : ∀ j i, MemLp (F j i) 2 volume) (hb : ∀ j, Integrable (b j))
    (hFzero : ∀ j i p, p 1 ≤ 0 → F j i p = 0)
    (hbzero : ∀ j p, p 1 ≤ 0 → b j p = 0)
    {u : LoopPlane → E} (hu : Continuous u)
    {V : Fin 2 → LoopPlane → E} (hV : ∀ i, MemLp (V i) 2 volume)
    (hw : ∀ i j, HasWeakPartialDeriv i (fun p => V i p j) (fun p => u p j) univ)
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hmap : MapsTo u A K) {f : Fin n → E → ℝ}
    (hf : ∀ j, ContDiffOn ℝ 1 (f j) U)
    {phi : LoopPlane → ℝ} (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi)
    (hs : tsupport phi ⊆ O) (hsA : tsupport phi ⊆ A)
    (hz : ∀ j, dirichlet j → ∀ p : LoopPlane, p 1 = 0 → phi p * f j (u p) = 0)
    (heq : ∀ j, ∀ psi : LoopPlane → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi →
      tsupport psi ⊆ O → (dirichlet j → ∀ p : LoopPlane, p 1 = 0 → psi p = 0) →
      (∫ p, ∑ i : Fin 2, F j i p * fderiv ℝ psi p (EuclideanSpace.single i 1)) =
        ∫ p, b j p * psi p) :
    (∫ p, ∑ i : Fin 2, (∑ j : Fin n, F j i p * f j (u p)) *
      fderiv ℝ phi p (EuclideanSpace.single i 1)) =
        ∫ p, phi p * ((∑ j : Fin n, b j p * f j (u p)) -
          ∑ i : Fin 2, ∑ j : Fin n,
            F j i p * fderiv ℝ (f j) (u p) (V i p)) := by
  classical
  have hI (j : Fin n) := compact_coefficient_products (hF j) (hb j) hu hV hw
    hU hK hKU hmap (hf j) hp hc hsA
  let X : Fin n → LoopPlane → ℝ := fun j p => ∑ i : Fin 2,
    F j i p * (phi p * fderiv ℝ (f j) (u p) (V i p))
  let Y : Fin n → LoopPlane → ℝ := fun j p => ∑ i : Fin 2,
    F j i p * (fderiv ℝ phi p (EuclideanSpace.single i 1) * f j (u p))
  let Z : Fin n → LoopPlane → ℝ := fun j p => b j p * (phi p * f j (u p))
  have hX (j : Fin n) : Integrable (X j) := integrable_finsetSum _ (fun i _ => (hI j).1 i)
  have hY (j : Fin n) : Integrable (Y j) := integrable_finsetSum _ (fun i _ => (hI j).2.1 i)
  have hZ (j : Fin n) : Integrable (Z j) := (hI j).2.2
  have htest (j : Fin n) : (∫ p, X j p) + (∫ p, Y j p) = ∫ p, Z j p := by
    rw [← integral_add (hX j) (hY j)]
    have hh := m64NaturalGrowth_compact_coefficient_face_test (dirichlet j) hO
      (hF j) (hb j) (hFzero j) (hbzero j) hu hV hw hU hK hKU hmap (hf j)
      hp hc hs hsA (hz j) (heq j)
    convert hh using 1
    congr 1
    funext p
    simp only [X, Y, ← Finset.sum_add_distrib, mul_add]
  have hsum : (∫ p, ∑ j : Fin n, Y j p) =
      (∫ p, ∑ j : Fin n, Z j p) - ∫ p, ∑ j : Fin n, X j p := by
    simp only [integral_finsetSum _ (fun j _ => hX j),
      integral_finsetSum _ (fun j _ => hY j), integral_finsetSum _ (fun j _ => hZ j)]
    have hh := congrArg (fun v : Fin n → ℝ => ∑ j, v j) (funext htest)
    simp only [Finset.sum_add_distrib] at hh
    linarith
  rw [← integral_sub (integrable_finsetSum _ (fun j _ => hZ j))
    (integrable_finsetSum _ (fun j _ => hX j))] at hsum
  convert hsum using 1
  · congr 1
    funext p
    simp only [Y, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  · congr 1
    funext p
    simp only [X, Z, mul_sub, Finset.mul_sum]
    rw [Finset.sum_comm (f := fun j i =>
      F j i p * (phi p * fderiv ℝ (f j) (u p) (V i p)))]
    congr 1
    · apply Finset.sum_congr rfl
      intro j _
      ring
    · apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

end PoincareConjecture
