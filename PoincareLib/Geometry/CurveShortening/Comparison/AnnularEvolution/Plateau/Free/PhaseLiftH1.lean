import PoincareLib.Geometry.CurveShortening.Comparison.Compatibility.SourceNames
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Free.PhaseLiftLocalH1
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Free.PhaseWeakLocality
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Free.PhaseCurrentColumns

/-! A continuous real lift of the actual weak circle observation is H1.
The oriented current supplies one explicit L2 column field. Local smooth
angles identify it, and weak locality proves the global derivative.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric Topology
open scoped ContDiff

namespace PoincareMT

open Poincare.Analysis.Sobolev.Weak Proofs.M58

/-- The explicit oriented circle current is the genuine global weak derivative of the
continuous real lift. Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem m64ContinuousPhase_weak_columns
    {O : Set LoopPlane} (hO : IsOpen O)
    {u : LoopPlane → ℝ} {q : LoopPlane → LoopPlane}
    {Z : Fin 2 → LoopPlane → LoopPlane} {k : ℝ} (hk : k ≠ 0)
    (hu : Continuous u) (hq : Continuous q) (huLp : MemLp u 2 (volume.restrict O))
    (hZ : ∀ i, MemLp (Z i) 2 (volume.restrict O))
    (hw : ∀ i j, HasWeakPartialDeriv i (fun p => Z i p j) (fun p => q p j) O)
    (hphase : ∀ p, q p = angularPoint (k * u p)) :
    let V := fun i p => k⁻¹ * M64.planarCircleCurrent (q p) (Z i p)
    (∀ i, MemLp (V i) 2 (volume.restrict O)) ∧
      (∀ i, HasWeakPartialDeriv i (V i) u O) ∧
      ∀ i, ∀ᵐ p ∂volume.restrict O, ‖Z i p‖ ^ 2 = k ^ 2 * (V i p) ^ 2 := by
  let V := fun i p => k⁻¹ * M64.planarCircleCurrent (q p) (Z i p)
  have hnorm (p : LoopPlane) : ‖q p‖ = 1 := by rw [hphase, norm_angularPoint]
  have hprod (i j l : Fin 2) : MemLp (fun p => q p j * Z i p l)
      2 (volume.restrict O) := by
    have hj : AEStronglyMeasurable (fun p => q p j) (volume.restrict O) :=
      ((EuclideanSpace.proj j).continuous.comp hq).aestronglyMeasurable
    apply ((hZ i).eval_piLp l).of_le_mul (c := 1)
      (hj.mul ((hZ i).eval_piLp l).aestronglyMeasurable)
    filter_upwards with p
    simp only [Pi.mul_apply]
    rw [norm_mul, one_mul]
    have hbound : ‖q p j‖ ≤ 1 := (PiLp.norm_apply_le (q p) j).trans_eq (hnorm p)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hbound (norm_nonneg (Z i p l))
  have hV (i : Fin 2) : MemLp (V i) 2 (volume.restrict O) :=
    ((hprod i 0 1).sub (hprod i 1 0)).const_mul k⁻¹
  have hweak (i : Fin 2) : HasWeakPartialDeriv i (V i) u O := by
    apply m64WeakPartial_of_local hO huLp (hV i)
    intro a ha
    obtain ⟨r, hr, hrO, hlocal⟩ :=
      m64ContinuousPhase_local_memW1p hO hk hu hq hZ hw hphase ha
    choose W hW hwW using hlocal.2
    have hsub : ball a r ⊆ O := ball_subset_closedBall.trans hrO
    have hcurrent := m64WeakPhase_circle_current isOpen_ball hlocal.1 hW hwW q Z
      (fun j => (hZ j).mono_measure (Measure.restrict_mono hsub le_rfl))
      (fun j l => (hw j l).restrict isOpen_ball hsub) k (Eventually.of_forall hphase)
    have hAE : W i =ᵐ[volume.restrict (ball a r)] V i := by
      filter_upwards [hcurrent i] with p hp
      dsimp only [V]
      rw [hp, ← mul_assoc, inv_mul_cancel₀ hk, one_mul]
    exact ⟨ball a r, isOpen_ball, mem_ball_self hr, hsub,
      m64WeakPartialDeriv_ae_congr EventuallyEq.rfl hAE (hwW i)⟩
  exact ⟨hV, hweak, m64WeakPhase_circle_column_norm_sq hO huLp hV hweak q Z hZ hw k
    (Eventually.of_forall hphase)⟩

/-- A continuous real lift of an H1 circle observation is H1 on the actual disk. Proof
expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem m64ContinuousPhase_disk_memW1p
    {u : LoopPlane → ℝ} {q : LoopPlane → LoopPlane}
    {Z : Fin 2 → LoopPlane → LoopPlane} {k : ℝ} (hk : k ≠ 0)
    (hu : Continuous u) (hq : Continuous q)
    (hZ : ∀ i, MemLp (Z i) 2 (volume.restrict (ball (0 : LoopPlane) 1)))
    (hw : ∀ i j, HasWeakPartialDeriv i (fun p => Z i p j) (fun p => q p j)
      (ball (0 : LoopPlane) 1))
    (hphase : ∀ p, q p = angularPoint (k * u p)) :
    MemW1p 2 u (ball (0 : LoopPlane) 1) := by
  have huLp : MemLp u 2 (volume.restrict (ball (0 : LoopPlane) 1)) := by
    apply (memLp_two_iff_integrable_sq hu.aestronglyMeasurable).mpr
    exact (hu.pow 2).continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : LoopPlane) 1) |>.mono_set ball_subset_closedBall
  obtain ⟨hV, hwV, -⟩ := m64ContinuousPhase_weak_columns isOpen_ball hk hu hq huLp hZ hw hphase
  exact ⟨huLp, fun i => ⟨_, hV i, hwV i⟩⟩

end PoincareMT
