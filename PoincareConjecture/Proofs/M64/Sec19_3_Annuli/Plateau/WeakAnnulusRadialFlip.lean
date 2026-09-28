import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.RadialFlipGeometry
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.VariableModulusEnergy












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M64ObservedWeakAnnulus

open Poincare.Analysis.Sobolev.Weak

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S
local notation "T" => m64AnnulusRadialFlip

set_option maxHeartbeats 800000 in



theorem exists_radial_flip (A : M64ObservedWeakAnnulus (n := n) e c0 c1) :
    ∃ W : M64ObservedWeakAnnulus (n := n) e c1 c0,
      W.map = A.map ∘ T ∧
      (∀ i, (W.column i : LoopPlane → E) =ᵐ[mu]
        fun p => (if i = 0 then (1 : ℝ) else -1) • A.column i (T p)) ∧
      ∀ (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (r : ℝ),
        W.weightedEnergy Q r = A.weightedEnergy Q r := by
  let sign := fun i : Fin 2 => if i = 0 then (1 : ℝ) else -1
  let f := A.map ∘ T
  let V := fun i p => sign i • A.column i (T p)
  have hmp := m64AnnulusRadialFlip_restrict_measurePreserving
  have hf : MemLp (e ∘ f) 2 mu := A.observed_memLp.comp_measurePreserving hmp
  have hV (i : Fin 2) : MemLp (V i) 2 mu :=
    ((Lp.memLp (A.column i)).comp_measurePreserving hmp).const_smul (sign i)
  let column := fun i => (hV i).toLp (V i)
  have hcoe (i : Fin 2) : column i =ᵐ[mu] V i := (hV i).coeFn_toLp
  have hweak (i : Fin 2) (b : Fin m) : HasWeakPartialDeriv i
      (fun p => V i p b) (fun p => e (f p) b) S := by
    intro phi hp hc hs
    have hpc : ContDiff ℝ ∞ (phi ∘ T) := hp.comp m64AnnulusRadialFlip_contDiff
    have hps : tsupport (phi ∘ T) ⊆ S := by
      rw [tsupport_comp_eq_preimage]
      intro p hpS
      have hTp : p ∈ T ⁻¹' S := hs hpS
      rwa [m64AnnulusRadialFlip_preimage_interior] at hTp
    have hA := A.weak_partial i b (phi ∘ T) hpc (hc.comp_homeomorph T) hps
    have hz : (∫ p in S, (phi ∘ T) p • A.column i p b) +
        (∫ p in S, fderiv ℝ (phi ∘ T) p (EuclideanSpace.single i 1) • e (A.map p) b) = 0 := by
      simp only [smul_eq_mul, mul_comm] at hA ⊢
      linarith
    have ht := m64AnnulusRadialFlip_green (fun p => e (A.map p) b)
      (fun p => A.column i p b) (hp.of_le (by simp)) i
    rw [hz, smul_zero] at ht
    simp only [smul_eq_mul] at ht
    change (∫ p in S, e (A.map (T p)) b * fderiv ℝ phi p (EuclideanSpace.single i 1)) =
      -(∫ p in S, (sign i • A.column i (T p)) b * phi p)
    simp only [PiLp.smul_apply, smul_eq_mul]
    dsimp only [sign] at *
    simp only [mul_comm] at ht ⊢
    linarith
  have hboundary (phi : LoopPlane → ℝ) (hp : ContDiff ℝ 1 phi) :
      (∫ p in S, phi p • V 1 p) +
        (∫ p in S, fderiv ℝ phi p (EuclideanSpace.single (1 : Fin 2) 1) • e (f p)) =
      ∫ x in Icc (0 : ℝ) curvePeriod,
        phi (annulusPoint x 1) • e (c0 x) - phi (annulusPoint x 0) • e (c1 x) := by
    have hpc : ContDiff ℝ 1 (phi ∘ T) :=
      hp.comp (m64AnnulusRadialFlip_contDiff.of_le (by simp))
    have ht := m64AnnulusRadialFlip_green (e ∘ A.map) (A.column 1) hp 1
    have hb := A.boundary (phi ∘ T) hpc
    simp only [Function.comp_apply] at ht hb
    rw [hb] at ht
    calc
      _ = -(∫ x in Icc (0 : ℝ) curvePeriod,
          (phi ∘ T) (annulusPoint x 1) • e (c1 x) -
            (phi ∘ T) (annulusPoint x 0) • e (c0 x)) := by simpa [V, f, sign] using ht
      _ = _ := by
        rw [← integral_neg]
        apply integral_congr_ae
        filter_upwards [] with x
        simp only [Function.comp_apply, m64AnnulusRadialFlip_point, sub_self, sub_zero, neg_sub]
  have hseam (phi : LoopPlane → ℝ) (hp : ContDiff ℝ 1 phi)
      (hs : ∀ s ∈ Icc (0 : ℝ) 1, phi (annulusPoint curvePeriod s) = phi (annulusPoint 0 s)) :
      (∫ p in S, phi p • V 0 p) +
        (∫ p in S, fderiv ℝ phi p (EuclideanSpace.single (0 : Fin 2) 1) • e (f p)) = 0 := by
    have hpc : ContDiff ℝ 1 (phi ∘ T) :=
      hp.comp (m64AnnulusRadialFlip_contDiff.of_le (by simp))
    have hs' : ∀ s ∈ Icc (0 : ℝ) 1,
        (phi ∘ T) (annulusPoint curvePeriod s) = (phi ∘ T) (annulusPoint 0 s) := by
      intro s hsI
      simp only [Function.comp_apply, m64AnnulusRadialFlip_point]
      exact hs (1 - s) ⟨by linarith [hsI.2], by linarith [hsI.1]⟩
    have ht := m64AnnulusRadialFlip_green (e ∘ A.map) (A.column 0) hp 0
    have hsA := A.seam (phi ∘ T) hpc hs'
    simp only [Function.comp_apply] at ht hsA
    rw [hsA, smul_zero] at ht
    simpa only [V, sign, f, Function.comp_apply] using ht
  let W : M64ObservedWeakAnnulus (n := n) e c1 c0 := {
    map := f
    observed_memLp := hf
    column := column
    tangent := fun i => by
      filter_upwards [hcoe i, hmp.quasiMeasurePreserving.ae (A.tangent i)] with p hp ht
      rw [hp]
      obtain ⟨v, hv⟩ := ht
      refine ⟨sign i • v, ?_⟩
      change mfderiv (𝓡 n) (𝓡 m) e (A.map (T p)) (sign i • v) = _
      rw [map_smul, hv]
    weak_partial := fun i b => m64WeakPartialDeriv_ae_congr EventuallyEq.rfl
      ((hcoe i).symm.mono fun p hp => congrArg (fun v : E => v b) hp) (hweak i b)
    boundary := fun phi hp => by
      have hc : (∫ p in S, phi p • column 1 p) = ∫ p in S, phi p • V 1 p :=
        integral_congr_ae ((hcoe 1).mono fun p hp => congrArg (fun v : E => phi p • v) hp)
      rw [hc]
      exact hboundary phi hp
    seam := fun phi hp hs => by
      have hc : (∫ p in S, phi p • column 0 p) = ∫ p in S, phi p • V 0 p :=
        integral_congr_ae ((hcoe 0).mono fun p hp => congrArg (fun v : E => phi p • v) hp)
      rw [hc]
      exact hseam phi hp hs }
  refine ⟨W, rfl, hcoe, ?_⟩
  intro Q r
  unfold weightedEnergy
  calc
    _ = ∫ p in S, (r * Q (A.map (T p)) (A.column 0 (T p)) (A.column 0 (T p)) +
        r⁻¹ * Q (A.map (T p)) (A.column 1 (T p)) (A.column 1 (T p))) / 2 := by
      apply integral_congr_ae
      filter_upwards [hcoe 0, hcoe 1] with p hp0 hp1
      change (r * Q (f p) (column 0 p) (column 0 p) +
        r⁻¹ * Q (f p) (column 1 p) (column 1 p)) / 2 = _
      rw [hp0, hp1]
      simp [V, sign, f]
    _ = _ := m64AnnulusRadialFlip_integral (fun p =>
      (r * Q (A.map p) (A.column 0 p) (A.column 0 p) +
        r⁻¹ * Q (A.map p) (A.column 1 p) (A.column 1 p)) / 2)

end PoincareConjecture.M64ObservedWeakAnnulus
