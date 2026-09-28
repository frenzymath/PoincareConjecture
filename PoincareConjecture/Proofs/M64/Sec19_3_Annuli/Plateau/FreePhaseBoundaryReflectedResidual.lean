import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreePhaseBoundaryZeroTraceExtension
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryOddReflection
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryCoordinateSwap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
open Poincare.Analysis.Sobolev.Weak
open Poincare.Analysis.Sobolev.BoundaryExtension
open Poincare.Analysis.Sobolev.BoundaryTangential

namespace PoincareConjecture

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

private theorem m64FreePhase_residual_face_zero
    {v : LoopPlane → E} (hv : Continuous v)
    (hvneg : ∀ p : LoopPlane, p 1 < 0 → v p = 0) :
    ∀ p : LoopPlane, p 1 = 0 → v p = 0 := by
  have hZ : IsClosed {p : LoopPlane | v p = 0} :=
    isClosed_eq hv continuous_const
  intro p hp
  apply (closure_minimal (fun q hq => hvneg q hq) hZ)
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  let q : LoopPlane := p - (ε / 2) • EuclideanSpace.single (1 : Fin 2) 1
  refine ⟨q, ?_, ?_⟩
  · change (p - (ε / 2) • EuclideanSpace.single (1 : Fin 2) 1 : LoopPlane) 1 < 0
    simp only [PiLp.sub_apply, PiLp.smul_apply, PiLp.single_apply, hp]
    norm_num
    exact hε
  · change dist p (p - (ε / 2) • EuclideanSpace.single (1 : Fin 2) 1) < ε
    rw [dist_self_sub_right, norm_smul]
    simp only [PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs,
      abs_of_pos (half_pos hε)]
    linarith

theorem m64FreePhase_boundary_reflected_residual_weak
    {u C : LoopPlane → E} {W : Fin 2 → LoopPlane → E}
    {a : LoopPlane} {R : ℝ} (hR : 0 < R) (ha : a 1 = 0)
    (hu : Continuous u) (hC : ContDiff ℝ 1 C)
    (hW : ∀ i, MemLp (W i) 2 (volume.restrict (ball a R)))
    (hw : ∀ i j, HasWeakPartialDeriv i (fun p => W i p j)
      (fun p => u p j) (ball a R))
    (htrace : ∀ p ∈ closedBall a R, p 1 ≤ 0 → u p = C p) :
    ∃ (v : LoopPlane → E) (dv : Fin 2 → LoopPlane → E),
      Continuous v ∧ HasCompactSupport v ∧
      (∀ p : LoopPlane, p 1 = 0 → v p = 0) ∧
      (∀ i, MemLp (dv i) 2 volume) ∧
      (∀ i j, HasWeakPartialDeriv i (fun p => dv i p j)
        (fun p => v p j) univ) ∧
      ∀ (j : Fin n) (i : Fin 2),
        HasWeakPartialDeriv i
          (m64BoundaryReflect (-coordinateSign i)
            (fun p => dv (Equiv.swap (0 : Fin 2) 1 i)
              (m64BoundaryCoordinateSwap p) j))
          (m64BoundaryReflect (-1)
            (fun p => v (m64BoundaryCoordinateSwap p) j)) univ := by
  obtain ⟨v, dv, hv, hvc, hvneg, hdv, hdweak, hW01p, hin⟩ :=
    m64FreePhase_boundary_zero_trace_extension hR ha hu hC hW hw htrace
  have hvface : ∀ p : LoopPlane, p 1 = 0 → v p = 0 :=
    m64FreePhase_residual_face_zero hv hvneg
  refine ⟨v, dv, hv, hvc, hvface, hdv, hdweak, ?_⟩
  intro j i
  let us : LoopPlane → ℝ := fun p => v (m64BoundaryCoordinateSwap p) j
  let vs : LoopPlane → ℝ := fun p =>
    dv (Equiv.swap (0 : Fin 2) 1 i) (m64BoundaryCoordinateSwap p) j
  have hus : Continuous us := by
    change Continuous ((EuclideanSpace.proj (𝕜 := ℝ) j) ∘ v ∘ m64BoundaryCoordinateSwap)
    exact (EuclideanSpace.proj (𝕜 := ℝ) j).continuous.comp
      (hv.comp m64BoundaryCoordinateSwap.continuous)
  have hvs : MemLp vs 2 (volume.restrict (halfSpace 2)) := by
    have hglobal : MemLp vs 2 volume := by
      dsimp only [vs]
      exact (hdv (Equiv.swap (0 : Fin 2) 1 i)).eval_piLp j |>.comp_measurePreserving
        m64BoundaryCoordinateSwap.measurePreserving
    exact hglobal.restrict (halfSpace 2)
  have husLp : MemLp us 2 (volume.restrict (halfSpace 2)) := by
    have hglobal : MemLp us 2 volume := by
      dsimp only [us]
      exact (hv.memLp_of_hasCompactSupport hvc).eval_piLp j |>.comp_measurePreserving
        m64BoundaryCoordinateSwap.measurePreserving
    exact hglobal.restrict (halfSpace 2)
  have huszero : ∀ p : LoopPlane, p 0 = 0 → us p = 0 := by
    intro p hp
    change (v (m64BoundaryCoordinateSwap p)) j = 0
    have hface : m64BoundaryCoordinateSwap p 1 = 0 := by
      simpa [m64BoundaryCoordinateSwap_apply] using hp
    rw [hvface (m64BoundaryCoordinateSwap p) hface]
    rfl
  have hvsweak : HasWeakPartialDeriv i vs us (halfSpace 2) := by
    have hswap := m64WeakPartialDeriv_coordinateSwap
      (S := (Set.univ : Set LoopPlane)) (u := fun p => v p j)
      (v := fun p => dv (Equiv.swap (0 : Fin 2) 1 i) p j)
      (i := i) (hdweak (Equiv.swap (0 : Fin 2) 1 i) j)
    have hswap' := hswap.restrict isOpen_halfSpace (subset_univ _)
    change HasWeakPartialDeriv i
      ((fun p => (dv (Equiv.swap (0 : Fin 2) 1 i) p).ofLp j) ∘
        m64BoundaryCoordinateSwap)
      ((fun p => (v p).ofLp j) ∘ m64BoundaryCoordinateSwap) (halfSpace 2)
    exact hswap'
  have href := m64ZeroTrace_boundaryReflect_weak i hus huszero husLp hvs hvsweak (-1)
  simpa only [us, vs, neg_one_mul] using href

end PoincareConjecture
