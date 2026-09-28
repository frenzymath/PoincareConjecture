import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakTargetTangency

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.WeakCompactness

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M] [T2Space M]

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S

theorem m64ObservedWeakAnnulus_subsequence
    (e : M → E) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e) (hei : IsClosedEmbedding e)
    (hread : M60.SUChartReadable (n := n) e) {c0 c1 : ℝ → M}
    (A : ℕ → M64ObservedWeakAnnulus (n := n) e c0 c1)
    {C : ℝ} (hC : ∀ j i, ‖(A j).column i‖ ^ 2 ≤ C) :
    ∃ (k : ℕ → ℕ) (L : M64ObservedWeakAnnulus (n := n) e c0 c1),
      StrictMono k ∧ Tendsto (fun j => (A (k j)).value) atTop (𝓝 L.value) ∧
      (∀ i, WeakConverges (fun j => (A (k j)).column i) (L.column i)) ∧
      ∀ᵐ p ∂mu, Tendsto (fun j => (A (k j)).map p) atTop (𝓝 (L.map p)) := by
  classical
  obtain ⟨R, hR⟩ := (isCompact_range he.continuous).isBounded.exists_norm_le
  have hnorm (j : ℕ) (i : Fin 2) : (∫ p in S, ‖(A j).column i p‖ ^ 2) ≤ C := by
    rw [← LpFiniteCoordinatesNative.l2_norm_sq]
    exact hC j i
  obtain ⟨k, U, W, hk, hstrong, hweak, hae⟩ := m64Annulus_weak_sobolev_subsequence
    (fun j => e ∘ (A j).map) (fun j i => (A j).column i)
    (fun j => (A j).observed_memLp) (fun j i => Lp.memLp ((A j).column i))
    (fun j i b => (A j).weak_partial i b) (fun _ _ => hR _ (mem_range_self _)) hnorm
  simp only [Lp.toLp_coeFn] at hweak
  have huweak : WeakConverges (fun j => (A (k j)).value) U :=
    fun T => (T.continuous.tendsto U).comp hstrong
  have htarget : ∀ᵐ p ∂mu, U p ∈ range e := by
    filter_upwards [hae] with p hp
    exact hei.isClosed_range.mem_of_tendsto hp
      (Eventually.of_forall fun j => mem_range_self ((A (k j)).map p))
  let v : LoopPlane → M := fun p =>
    if hp : U p ∈ range e then Classical.choose hp else (A 0).map 0
  have hev : ∀ᵐ p ∂mu, e (v p) = U p := by
    filter_upwards [htarget] with p hp
    simp only [v, dif_pos hp]
    exact Classical.choose_spec hp
  have hlim : ∀ᵐ p ∂mu, Tendsto (fun j => (A (k j)).map p) atTop (𝓝 (v p)) := by
    filter_upwards [hae, hev] with p hp hpv
    apply hei.isEmbedding.tendsto_nhds_iff.mpr
    rw [hpv]
    exact hp
  have hv : MemLp (e ∘ v) 2 mu := (Lp.memLp U).ae_eq (EventuallyEq.symm hev)
  have htangent (i : Fin 2) : ∀ᵐ p ∂mu, W i p ∈ range (mfderiv (𝓡 n) (𝓡 m) e (v p)) :=
    m64WeakAnnulus_tangent_closed e he hei.isEmbedding hread (fun j => A (k j))
      v (W i) i (hweak i) hlim
  have hpartial (i : Fin 2) (b : Fin m) :
      Poincare.Analysis.Sobolev.Weak.HasWeakPartialDeriv i
        (fun p => W i p b) (fun p => e (v p) b) S := by
    apply m64WeakPartialDeriv_ae_congr
      ((EventuallyEq.symm hev).mono fun _ hp => congrArg (fun x : E => x b) hp)
      EventuallyEq.rfl
    apply m64Annulus_weak_partial_closed huweak (hweak i) i b
    intro j
    exact m64WeakPartialDeriv_ae_congr
      ((A (k j)).observed_memLp.coeFn_toLp.symm.mono
        fun _ hp => congrArg (fun x : E => x b) hp) EventuallyEq.rfl ((A (k j)).weak_partial i b)
  have htest (phi : LoopPlane → ℝ) (i : Fin 2) (c : E)
      (hphi : ContDiff ℝ 1 phi)
      (hseq : ∀ j, (∫ p in S, phi p • (A (k j)).column i p) +
        (∫ p in S, fderiv ℝ phi p (EuclideanSpace.single i 1) • e ((A (k j)).map p)) = c) :
      (∫ p in S, phi p • W i p) +
        (∫ p in S, fderiv ℝ phi p (EuclideanSpace.single i 1) • e (v p)) = c := by
    have hseq' (j : ℕ) : (∫ p in S, phi p • (A (k j)).column i p) +
        (∫ p in S, fderiv ℝ phi p (EuclideanSpace.single i 1) • (A (k j)).value p) = c := by
      convert hseq j using 2
      apply integral_congr_ae
      filter_upwards [(A (k j)).observed_memLp.coeFn_toLp] with p hp
      exact congrArg (fun x : E => fderiv ℝ phi p (EuclideanSpace.single i 1) • x) hp
    have hh := m64Annulus_weak_green_closed huweak (hweak i) i phi hphi c hseq'
    convert hh using 2
    apply integral_congr_ae
    filter_upwards [hev] with p hp
    exact congrArg (fun x : E => fderiv ℝ phi p (EuclideanSpace.single i 1) • x) hp
  let L : M64ObservedWeakAnnulus (n := n) e c0 c1 :=
    { map := v
      observed_memLp := hv
      column := W
      tangent := htangent
      weak_partial := hpartial
      boundary := fun phi hphi => htest phi 1 _ hphi
        (fun j => (A (k j)).boundary phi hphi)
      seam := fun phi hphi hseam => htest phi 0 0 hphi
        (fun j => (A (k j)).seam phi hphi hseam) }
  have hvalue : L.value = U := by
    apply Lp.ext
    exact hv.coeFn_toLp.trans hev
  refine ⟨k, L, hk, ?_, hweak, hlim⟩
  rwa [hvalue]

end PoincareConjecture
