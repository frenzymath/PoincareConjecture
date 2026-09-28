import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Boundary.StandardAnnulus
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.AnnulusPeriodMap
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonStandardQuotientPL












set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V1" => (Fin 1 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D1" => closedBall (0 : V1) 1
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "C" => AddCircle (4 * (128 : ℝ))
local notation "C32" => AddCircle (4 * (8 : ℝ))
local notation "Ann" => squareAnnulus 8 1



theorem standardTargetAnnulus_period_coordinates (theta : C)
    (z : C32 × Icc (-1 : ℝ) 1) :
    (standardTargetAnnulus theta
      ((exists_annulus_homeomorph (by norm_num : (0 : ℝ) < 8)
        (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : 4 * (1 : ℝ) < 8)).choose z) : X) =
      (standardPhaseCoordinates theta
        (originalIntervalCoordinates z.2,
          AddCircle.homeomorphAddCircle (4 * (8 : ℝ)) (4 * (128 : ℝ))
            (by norm_num) (by norm_num) z.1) : X) := by
  simp [standardTargetAnnulus, Dehn.annulusCylinderHomeomorph,
    standardAnnulusCylinderCoordinates, Prod.map, Prod.swap]



theorem exists_standardTargetAnnulus_polyhedral_parameter
    {β : Type*} {d : β → OpenPartialHomeomorph X V3}
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d) (theta : C) :
    ∃ q : (ℝ × ℝ) → X, PolyhedralPLInCharts d q Ann ∧
      ∀ x : Ann, (standardTargetAnnulus theta x : X) = q x := by
  classical
  obtain ⟨r, rfl⟩ := Quotient.exists_rep theta
  let scale : C32 ≃ₜ C := AddCircle.homeomorphAddCircle
    (4 * (8 : ℝ)) (4 * (128 : ℝ)) (by norm_num) (by norm_num)
  let a : C32 × Icc (-1 : ℝ) 1 → X := fun z =>
    standardPhaseCoordinates (r : C) (originalIntervalCoordinates z.2, scale z.1)
  let v : (ℝ × ℝ) →ᴬ[ℝ] ((Fin 1 ⊕ Fin 2) → ℝ) :=
    (ContinuousLinearMap.pi fun i : Fin 1 ⊕ Fin 2 => (match i with
      | Sum.inl _ => ContinuousLinearMap.snd ℝ ℝ ℝ
      | Sum.inr j => if j = 0 then
          (16 : ℝ) • (ContinuousLinearMap.fst ℝ ℝ ℝ)
        else 0 : (ℝ × ℝ) →L[ℝ] ℝ)).toContinuousAffineMap +
      ContinuousAffineMap.const ℝ (ℝ × ℝ) (Sum.elim (fun _ => 0) ![0, r])
  let phi : (ℝ × ℝ) → X := latticeCoordinateProjection (Fin 1) (Fin 2) L ∘ v
  have hphi : PolyhedralPLInCharts d phi (rectangle (4 * (8 : ℝ)) 1) := by
    obtain ⟨K, hK, hKs, _⟩ := finitePiecewiseAffineOn_wrappedStripMap
      (by norm_num : (0 : ℝ) < 1) (by norm_num : 4 * (1 : ℝ) < 8)
    apply hd.polyhedralPL_projection
    exact ⟨K, hK, hKs, K.affineOnFaces_affine v⟩
  have ha (s : ℝ) (_hs : s ∈ Icc 0 (4 * (8 : ℝ)))
      (t : Icc (-1 : ℝ) 1) : a ((s : C32), t) = phi (s, t) := by
    have hscale : scale (s : C32) = ((16 * s : ℝ) : C) := by
      rw [AddCircle.homeomorphAddCircle_apply_mk]
      norm_num [mul_comm]
    simp only [a, hscale]
    apply Prod.ext
    · funext i
      simp [phi, latticeCoordinateProjection, v, standardPhaseCoordinates,
        originalIntervalCoordinates]
      rfl
    · apply congrArg QuotientAddGroup.mk
      funext i
      fin_cases i <;> simp [v]
  obtain ⟨A, q, hA, hq, hqA, _, _⟩ := _root_.Dehn.exists_square_annulus_map_of_period
    hd.domain.compatible (by norm_num : (0 : ℝ) < 1)
    (by norm_num : 4 * (1 : ℝ) < 8) phi hphi a ha
  refine ⟨q, hq, ?_⟩
  intro x
  let A0 := (exists_annulus_homeomorph (by norm_num : (0 : ℝ) < 8)
    (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : 4 * (1 : ℝ) < 8)).choose
  have hA0 := (exists_annulus_homeomorph (by norm_num : (0 : ℝ) < 8)
    (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : 4 * (1 : ℝ) < 8)).choose_spec
  have heq (z : C32 × Icc (-1 : ℝ) 1) : A z = A0 z :=
    Subtype.ext ((hA z).trans (hA0 z).symm)
  have hx : A (A0.symm x) = x := (heq _).trans (A0.apply_symm_apply x)
  rw [← hx, hqA, heq]
  exact standardTargetAnnulus_period_coordinates (r : C) (A0.symm x)

end PoincareConjecture.M76.HamiltonIntervalTorus
