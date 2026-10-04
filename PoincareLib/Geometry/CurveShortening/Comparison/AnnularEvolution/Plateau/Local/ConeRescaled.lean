import PoincareLib.Geometry.CurveShortening.Comparison.Compatibility.SourceNames
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Local.ConeWeakFilling
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Local.ConeAffine

/-!
# Literal H1 cone fillings on arbitrary local disks

The map is composed with the positive affine normalization; each actual
weak column acquires the inverse radius. Green flux acquires the radius,
while the two-dimensional intrinsic energy is unchanged.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology Manifold ContDiff

namespace PoincareMT

open Proofs.M58 Poincare.Analysis.Sobolev.Weak

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)} {gamma : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => ball (0 : LoopPlane) 1

namespace M64ObservedConeDisk

/-- The actual cone disk pulled back by positive affine normalization. Proof expansion for
Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
def affineMap (A : M64ObservedConeDisk (n := n) e gamma) (a : LoopPlane) (r : ℝ) :
    LoopPlane → M := A.map ∘ m64ConeNormalize a r

/-- The literal affine cone column includes the inverse-radius derivative factor. Proof
expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
def affineColumn (A : M64ObservedConeDisk (n := n) e gamma) (a : LoopPlane) (r : ℝ)
    (i : Fin 2) (p : LoopPlane) : E := r⁻¹ • A.column i (m64ConeNormalize a r p)

/-- The actual affine cone map is continuous. Proof expansion for Morgan-Tian (2007), Lemma
19.15, pp. 447-449. -/
theorem affine_continuous (A : M64ObservedConeDisk (n := n) e gamma)
    (a : LoopPlane) (r : ℝ) : Continuous (A.affineMap a r) :=
  A.continuous.comp (m64ConeNormalize_continuous a r)

/-- The actual affine cone has exactly the prescribed trace on the translated circle. Proof
expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem affine_boundary (A : M64ObservedConeDisk (n := n) e gamma)
    (a : LoopPlane) {r : ℝ} (hr : 0 < r) (t : ℝ) :
    A.affineMap a r (a + r • angularPoint t) = gamma t := by
  rw [affineMap, Function.comp_apply, m64ConeNormalize_apply a hr, A.boundary]

/-- Positive affine normalization preserves the actual cone map's L2 integrability. Proof
expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem affine_memLp (A : M64ObservedConeDisk (n := n) e gamma)
    (a : LoopPlane) {r : ℝ} (hr : 0 < r) :
    MemLp (e ∘ A.affineMap a r) 2 (volume.restrict (ball a r)) :=
  m64ConeNormalize_memLp A.observed_memLp a hr

/-- Positive affine normalization preserves the actual cone columns' L2 integrability. Proof
expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem affine_column_memLp (A : M64ObservedConeDisk (n := n) e gamma)
    (a : LoopPlane) {r : ℝ} (hr : 0 < r) (i : Fin 2) :
    MemLp (A.affineColumn a r i) 2 (volume.restrict (ball a r)) :=
  (m64ConeNormalize_memLp (Lp.memLp (A.column i)) a hr).const_smul r⁻¹

/-- Affine cone columns stay in the actual target tangent range. Proof expansion for
Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem affine_tangent (A : M64ObservedConeDisk (n := n) e gamma)
    (a : LoopPlane) {r : ℝ} (hr : 0 < r) (i : Fin 2) :
    ∀ᵐ p ∂volume.restrict (ball a r),
      A.affineColumn a r i p ∈ range (mfderiv (𝓡 n) (𝓡 m) e (A.affineMap a r p)) := by
  have ht := (m64ConeNormalize_quasiMeasurePreserving a hr).ae (A.tangent i)
  filter_upwards [ht] with p hp
  obtain ⟨v, hv⟩ := hp
  refine ⟨r⁻¹ • v, ?_⟩
  change mfderiv (𝓡 n) (𝓡 m) e (A.map (m64ConeNormalize a r p)) (r⁻¹ • v) = _
  rw [map_smul, hv]
  rfl

/-- The literal inverse-radius columns are weak derivatives of the actual affine cone map.
Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem affine_weak_partial (A : M64ObservedConeDisk (n := n) e gamma)
    (a : LoopPlane) {r : ℝ} (hr : 0 < r) (i : Fin 2) (b : Fin m) :
    HasWeakPartialDeriv i (fun p => A.affineColumn a r i p b)
      (fun p => e (A.affineMap a r p) b) (ball a r) := by
  have hh := M60.suAffine_weakPartial (A.weak_partial i b) (-(r⁻¹ • a)) (inv_pos.mpr hr)
  have hN (p : LoopPlane) : -(r⁻¹ • a) + r⁻¹ • p = m64ConeNormalize a r p :=
    congrFun (m64ConeNormalize_affine a r) p
  simpa only [hN, m64ConeNormalize_preimage_ball a hr, affineMap, affineColumn,
    Function.comp_apply, PiLp.smul_apply, smul_eq_mul] using hh

/-- The actual affine cone Green identity retains the physical radius multiplying its
boundary flux. Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem affine_green (A : M64ObservedConeDisk (n := n) e gamma)
    (a : LoopPlane) {r : ℝ} (hr : 0 < r)
    (phi : LoopPlane → ℝ) (hphi : ContDiff ℝ 1 phi) (i : Fin 2) :
    (∫ p in ball a r, phi p • A.affineColumn a r i p) +
      (∫ p in ball a r, fderiv ℝ phi p (EuclideanSpace.single i 1) •
        e (A.affineMap a r p)) =
      r • ∫ t in Icc (-Real.pi) Real.pi,
        angularPoint t i • (phi (a + r • angularPoint t) • e (gamma t)) := by
  let psi := fun z : LoopPlane => phi (a + r • z)
  have hpsi : ContDiff ℝ 1 psi :=
    hphi.comp (contDiff_const.add (contDiff_id.const_smul r))
  have hd (z : LoopPlane) : fderiv ℝ psi z (EuclideanSpace.single i 1) =
      r * fderiv ℝ phi (a + r • z) (EuclideanSpace.single i 1) := by
    rw [show psi = (fun z : LoopPlane => phi (a + r • z)) from rfl, M60.suRescale_fderiv]
    rfl
  have hleft : (∫ p in ball a r, phi p • A.affineColumn a r i p) =
      r • ∫ z in S, psi z • A.column i z := by
    rw [m64ConeAffine_integral _ a hr, ← integral_smul]
    apply integral_congr_ae
    filter_upwards [] with z
    simp only [affineColumn, m64ConeNormalize_apply a hr, smul_smul, psi]
    congr 1
    field_simp [hr.ne']
  have hright : (∫ p in ball a r, fderiv ℝ phi p (EuclideanSpace.single i 1) •
        e (A.affineMap a r p)) =
      r • ∫ z in S, fderiv ℝ psi z (EuclideanSpace.single i 1) • e (A.map z) := by
    rw [m64ConeAffine_integral _ a hr, ← integral_smul]
    apply integral_congr_ae
    filter_upwards [] with z
    simp only [affineMap, Function.comp_apply, m64ConeNormalize_apply a hr, hd, smul_smul]
    congr 1
    ring
  rw [hleft, hright, ← smul_add, A.green psi hpsi i]

/-- Positive affine rescaling preserves the actual two-dimensional intrinsic cone energy.
Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem affine_energy (A : M64ObservedConeDisk (n := n) e gamma)
    (a : LoopPlane) {r : ℝ} (hr : 0 < r)
    (B : M → E →L[ℝ] E →L[ℝ] ℝ) :
    (∫ p in ball a r,
      (B (A.affineMap a r p) (A.affineColumn a r 0 p) (A.affineColumn a r 0 p) +
        B (A.affineMap a r p) (A.affineColumn a r 1 p) (A.affineColumn a r 1 p)) / 2) =
      A.energy B := by
  rw [m64ConeAffine_integral _ a hr]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [affineMap, affineColumn, Function.comp_apply, m64ConeNormalize_apply a hr,
    map_smul, smul_apply, smul_eq_mul]
  field_simp [hr.ne']

end M64ObservedConeDisk

end PoincareMT
