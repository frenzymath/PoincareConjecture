import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRadialH1Filling
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRadialDiskGreen
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.LocalConeAffine

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

open Proofs.M58 Poincare.Analysis.Sobolev.Weak

theorem m64ConeNormalize_preimage_closedBall (a : LoopPlane) {r : ℝ} (hr : 0 < r) :
    m64ConeNormalize a r ⁻¹' closedBall 0 1 = closedBall a r := by
  ext p
  simp only [mem_preimage, m64ConeNormalize, mem_closedBall, dist_eq_norm, sub_zero, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
  rw [← div_eq_inv_mul, div_le_iff₀ hr, one_mul]

theorem m64ConeNormalize_lower {a p : LoopPlane} (ha : a 1 = 0)
    {r : ℝ} (hr : 0 < r) (hp : p 1 ≤ 0) : m64ConeNormalize a r p 1 ≤ 0 := by
  simp only [m64ConeNormalize, PiLp.smul_apply, PiLp.sub_apply, ha, sub_zero, smul_eq_mul]
  exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hr.le) hp

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => ball (0 : LoopPlane) 1
local notation "K" => closedBall (0 : LoopPlane) 1
local notation "mu" => volume.restrict S

theorem m64RadialDisk_affine_data
    (e : M → E) (F : LoopPlane → M) (W : Fin 2 → LoopPlane → E)
    (hc : ContinuousOn F K) (hu : MemLp (e ∘ F) 2 mu) (hW : ∀ i, MemLp (W i) 2 mu)
    (ht : ∀ i, ∀ᵐ p ∂mu, W i p ∈ range (mfderiv (𝓡 n) (𝓡 m) e (F p)))
    (hw : ∀ i b, HasWeakPartialDeriv i (fun p => W i p b) (fun p => e (F p) b) S)
    (a : LoopPlane) {r : ℝ} (hr : 0 < r) :
    let f := F ∘ m64ConeNormalize a r
    let V := fun i p => r⁻¹ • W i (m64ConeNormalize a r p)
    ContinuousOn f (closedBall a r) ∧ MemLp (e ∘ f) 2 (volume.restrict (ball a r)) ∧
      (∀ i, MemLp (V i) 2 (volume.restrict (ball a r))) ∧
      (∀ i, ∀ᵐ p ∂volume.restrict (ball a r),
        V i p ∈ range (mfderiv (𝓡 n) (𝓡 m) e (f p))) ∧
      ∀ i b, HasWeakPartialDeriv i (fun p => V i p b) (fun p => e (f p) b) (ball a r) := by
  intro f V
  refine ⟨hc.comp (m64ConeNormalize_continuous a r).continuousOn ?_,
    m64ConeNormalize_memLp hu a hr,
    fun i => (m64ConeNormalize_memLp (hW i) a hr).const_smul r⁻¹, ?_, ?_⟩
  · intro p hp
    exact (show p ∈ m64ConeNormalize a r ⁻¹' K from by
      rwa [m64ConeNormalize_preimage_closedBall a hr])
  · intro i
    filter_upwards [(m64ConeNormalize_quasiMeasurePreserving a hr).ae (ht i)] with p hp
    obtain ⟨v, hv⟩ := hp
    refine ⟨r⁻¹ • v, ?_⟩
    change mfderiv (𝓡 n) (𝓡 m) e (F (m64ConeNormalize a r p)) (r⁻¹ • v) = _
    rw [map_smul, hv]
  · intro i b
    have hh := M60.suAffine_weakPartial (hw i b) (-(r⁻¹ • a)) (inv_pos.mpr hr)
    have hN (p : LoopPlane) : -(r⁻¹ • a) + r⁻¹ • p = m64ConeNormalize a r p :=
      congrFun (m64ConeNormalize_affine a r) p
    simpa only [hN, m64ConeNormalize_preimage_ball a hr, f, V,
      Function.comp_apply, PiLp.smul_apply, smul_eq_mul] using hh

theorem m64RadialDisk_affine_green
    (u : LoopPlane → E) (W : Fin 2 → LoopPlane → E)
    (hu : MemLp u 2 mu) (hW : ∀ i, MemLp (W i) 2 mu)
    (hw : ∀ i b, HasWeakPartialDeriv i (fun p => W i p b) (fun p => u p b) S)
    (hc : ContinuousOn u K) (a : LoopPlane) {r : ℝ} (hr : 0 < r)
    (phi : LoopPlane → ℝ) (hphi : ContDiff ℝ 1 phi) (i : Fin 2) :
    (∫ p in ball a r, phi p • (r⁻¹ • W i (m64ConeNormalize a r p))) +
      (∫ p in ball a r, fderiv ℝ phi p (EuclideanSpace.single i 1) •
        u (m64ConeNormalize a r p)) =
      r • ∫ t in Icc (-Real.pi) Real.pi,
        angularPoint t i • (phi (a + r • angularPoint t) • u (angularPoint t)) := by
  let psi := fun z : LoopPlane => phi (a + r • z)
  have hpsi : ContDiff ℝ 1 psi :=
    hphi.comp (contDiff_const.add (contDiff_id.const_smul r))
  have hd (z : LoopPlane) : fderiv ℝ psi z (EuclideanSpace.single i 1) =
      r * fderiv ℝ phi (a + r • z) (EuclideanSpace.single i 1) := by
    rw [show psi = (fun z : LoopPlane => phi (a + r • z)) from rfl, M60.suRescale_fderiv]
    rfl
  have hleft : (∫ p in ball a r, phi p • (r⁻¹ • W i (m64ConeNormalize a r p))) =
      r • ∫ z in S, psi z • W i z := by
    rw [m64ConeAffine_integral _ a hr, ← integral_smul]
    apply integral_congr_ae
    filter_upwards [] with z
    simp only [m64ConeNormalize_apply a hr, smul_smul, psi]
    congr 1
    field_simp [hr.ne']
  have hright : (∫ p in ball a r, fderiv ℝ phi p (EuclideanSpace.single i 1) •
        u (m64ConeNormalize a r p)) =
      r • ∫ z in S, fderiv ℝ psi z (EuclideanSpace.single i 1) • u z := by
    rw [m64ConeAffine_integral _ a hr, ← integral_smul]
    apply integral_congr_ae
    filter_upwards [] with z
    simp only [m64ConeNormalize_apply a hr, hd, smul_smul]
    congr 1
    ring
  rw [hleft, hright, ← smul_add, m64ContinuousH1Disk_green u W hu hW hw hc psi hpsi i]

theorem m64RadialDisk_affine_column_energy
    (W : LoopPlane → E) (a : LoopPlane) {r : ℝ} (hr : 0 < r) :
    (∫ p in ball a r, ‖r⁻¹ • W (m64ConeNormalize a r p)‖ ^ 2) = ∫ z in S, ‖W z‖ ^ 2 := by
  rw [m64ConeAffine_integral _ a hr]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [m64ConeNormalize_apply a hr, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr hr.le), smul_eq_mul]
  field_simp [hr.ne']

omit [TopologicalSpace M] in

theorem m64RadialDisk_affine_energy
    (F : LoopPlane → M) (W : Fin 2 → LoopPlane → E)
    (a : LoopPlane) {r : ℝ} (hr : 0 < r) (Q : M → E →L[ℝ] E →L[ℝ] ℝ) :
    (∫ p in ball a r,
      (Q (F (m64ConeNormalize a r p)) (r⁻¹ • W 0 (m64ConeNormalize a r p))
        (r⁻¹ • W 0 (m64ConeNormalize a r p)) +
        Q (F (m64ConeNormalize a r p)) (r⁻¹ • W 1 (m64ConeNormalize a r p))
          (r⁻¹ • W 1 (m64ConeNormalize a r p))) / 2) =
      ∫ z in S, (Q (F z) (W 0 z) (W 0 z) + Q (F z) (W 1 z) (W 1 z)) / 2 := by
  rw [m64ConeAffine_integral _ a hr]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [m64ConeNormalize_apply a hr, map_smul, smul_apply, smul_eq_mul]
  field_simp [hr.ne']

end PoincareConjecture
