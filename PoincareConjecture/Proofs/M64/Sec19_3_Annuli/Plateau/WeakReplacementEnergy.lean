import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakAnnulusReplacement












set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S




theorem m64Observed_energyDensity_integrable
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q)
    {C : ℝ} (hb : ∀ q, ‖Q q‖ ≤ C)
    {K : Set LoopPlane} (f : LoopPlane → M)
    (hf : AEStronglyMeasurable f (volume.restrict K))
    (V : Fin 2 → LoopPlane → E) (hV : ∀ i, MemLp (V i) 2 (volume.restrict K)) :
    IntegrableOn (fun p => (Q (f p) (V 0 p) (V 0 p) + Q (f p) (V 1 p) (V 1 p)) / 2)
      K volume := by
  have hi (i : Fin 2) : IntegrableOn (fun p => Q (f p) (V i p) (V i p)) K volume := by
    have hc : Continuous (fun q : (E →L[ℝ] E →L[ℝ] ℝ) × E => q.1 q.2 q.2) :=
      (continuous_fst.clm_apply continuous_snd).clm_apply continuous_snd
    have hm := hc.comp_aestronglyMeasurable
      ((hQ.comp_aestronglyMeasurable hf).prodMk (hV i).aestronglyMeasurable)
    have hv := (memLp_two_iff_integrable_sq_norm (hV i).aestronglyMeasurable).mp (hV i)
    apply (hv.const_mul C).mono' hm
    filter_upwards [] with p
    change ‖Q (f p) (V i p) (V i p)‖ ≤ C * ‖V i p‖ ^ 2
    have hnorm := (Q (f p)).le_opNorm₂ (V i p) (V i p)
    have hmul := mul_le_mul_of_nonneg_right (hb (f p)) (sq_nonneg ‖V i p‖)
    nlinarith
  exact ((hi 0).add (hi 1)).div_const 2




theorem m64WeakAnnulusReplacement_energy
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q) (hei : IsEmbedding e)
    {C : ℝ} (hb : ∀ q, ‖Q q‖ ≤ C)
    (A W : M64ObservedWeakAnnulus (n := n) e c0 c1)
    {K : Set LoopPlane} [DecidablePred (· ∈ K)] (hK : MeasurableSet K) (hKS : K ⊆ S)
    (f : LoopPlane → M) (hf : AEStronglyMeasurable f (volume.restrict K))
    (V : Fin 2 → LoopPlane → E) (hV : ∀ i, MemLp (V i) 2 (volume.restrict K))
    (hmap : W.map = K.piecewise f A.map)
    (hcol : ∀ i, (W.column i : LoopPlane → E) =ᵐ[mu] K.piecewise (V i) (A.column i)) :
    W.energy Q = A.energy Q +
      (∫ p in K, (Q (f p) (V 0 p) (V 0 p) + Q (f p) (V 1 p) (V 1 p)) / 2) -
      ∫ p in K, (Q (A.map p) (A.column 0 p) (A.column 0 p) +
        Q (A.map p) (A.column 1 p) (A.column 1 p)) / 2 := by
  classical
  let old := fun p => (Q (A.map p) (A.column 0 p) (A.column 0 p) +
    Q (A.map p) (A.column 1 p) (A.column 1 p)) / 2
  let new := fun p => (Q (f p) (V 0 p) (V 0 p) + Q (f p) (V 1 p) (V 1 p)) / 2
  have heq : (fun p => (Q (W.map p) (W.column 0 p) (W.column 0 p) +
      Q (W.map p) (W.column 1 p) (W.column 1 p)) / 2) =ᵐ[mu] K.piecewise new old := by
    filter_upwards [hcol 0, hcol 1] with p h0 h1
    rw [h0, h1, hmap]
    by_cases hp : p ∈ K <;> simp only [piecewise, hp, if_true, if_false, new, old]
  unfold M64ObservedWeakAnnulus.energy
  rw [integral_congr_ae heq]
  exact m64Integral_piecewise_of_subset hK hKS
    (m64Observed_energyDensity_integrable Q hQ hb f hf V hV) (A.energy_integrable Q hQ hei hb)



theorem M64ObservedWeakAnnulus.local_energy_le_of_matching_flux
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q) (hei : IsEmbedding e)
    {C : ℝ} (hb : ∀ q, ‖Q q‖ ≤ C)
    (hmin : ∀ W : M64ObservedWeakAnnulus (n := n) e c0 c1, A.energy Q ≤ W.energy Q)
    {K : Set LoopPlane} (hK : MeasurableSet K) (hKS : K ⊆ S)
    (f : LoopPlane → M) (hf : AEStronglyMeasurable f (volume.restrict K))
    (V : Fin 2 → LoopPlane → E) (hV : ∀ i, MemLp (V i) 2 (volume.restrict K))
    (hfl : MemLp (e ∘ f) 2 (volume.restrict K))
    (ht : ∀ i, ∀ᵐ p ∂volume.restrict K,
      V i p ∈ range (mfderiv (𝓡 n) (𝓡 m) e (f p)))
    (hgreen : ∀ (phi : LoopPlane → ℝ), ContDiff ℝ 1 phi → ∀ i : Fin 2,
      (∫ p in K, phi p • V i p) +
        (∫ p in K, fderiv ℝ phi p (EuclideanSpace.single i 1) • e (f p)) =
      (∫ p in K, phi p • A.column i p) +
        (∫ p in K, fderiv ℝ phi p (EuclideanSpace.single i 1) • e (A.map p))) :
    (∫ p in K, (Q (A.map p) (A.column 0 p) (A.column 0 p) +
      Q (A.map p) (A.column 1 p) (A.column 1 p)) / 2) ≤
      ∫ p in K, (Q (f p) (V 0 p) (V 0 p) + Q (f p) (V 1 p) (V 1 p)) / 2 := by
  classical
  obtain ⟨W, hmap, hcol⟩ := A.replace hK hKS f V hfl hV ht hgreen
  have hE := m64WeakAnnulusReplacement_energy Q hQ hei hb A W hK hKS f hf V hV hmap hcol
  have hm := hmin W
  linarith

end PoincareConjecture
