import PoincareConjecture.Proofs.M76.Rigidity.StandardHierarchyCuts
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonStandardQuotientPL
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductBall
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervals
import PoincareConjecture.Proofs.M76.Mathlib.HamiltonHandleCubeBall

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V0" => (Fin 0 → ℝ)
local notation "V1" => (Fin 1 → ℝ)
local notation "D1" => closedBall (0 : V1) 1
local notation "L0" => hamiltonZeroPeriodLattice
local notation "L1" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "X1" => LatticeHandleAmbient (Fin 1) (Fin 2) L1
local notation "p0" => (4 * (16 : ℝ))
local notation "p1" => (4 * (128 : ℝ))
local notation "C0" => AddCircle p0
local notation "C1" => AddCircle p1

private theorem finiteAffine_on_ballPair
    {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup M] [NormedSpace ℝ M]
    {S B : Set E} (hS : IsFinitePLBallPair M S B) (a : E →ᴬ[ℝ] F) :
    FinitePiecewiseAffineOn a S := by
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKS, _⟩, _⟩, _⟩ := hS
  exact ⟨K, hK, hKS, K.affineOnFaces_affine a⟩

def hamiltonZeroTorusParameter (z : ℝ × ℝ) : X0 :=
  (0, QuotientAddGroup.mk ![z.1, z.2, 0])

def hamiltonZeroCutParameter (z : (ℝ × ℝ) × ℝ) : X0 :=
  (0, QuotientAddGroup.mk ![z.1.1, z.1.2, z.2])

def hamiltonOneAnnulusParameter (z : V1 × ℝ) : X1 :=
  (z.1, QuotientAddGroup.mk ![z.2, 0])

def hamiltonOneCutParameter (z : (V1 × ℝ) × ℝ) : X1 :=
  (z.1.1, QuotientAddGroup.mk ![z.1.2, z.2])

theorem hamiltonZeroTorusParameter_eq_surface (s t : ℝ) :
    ((latticeHandleDomainEquiv (Fin 0) (Fin 3) L0).symm
      (hamiltonZeroHierarchyTorus ((s : C0), (t : C0))) : X0) =
        hamiltonZeroTorusParameter (s, t) := by
  have he := hamiltonZeroHierarchyCut_coe s t 0
  rw [(hamiltonZeroHierarchyCut_endpoints ((s : C0), (t : C0))).1] at he
  rw [he]
  rfl

theorem hamiltonZeroCutParameter_eq_cut (s t u : ℝ) :
    ((latticeHandleDomainEquiv (Fin 0) (Fin 3) L0).symm
      (hamiltonZeroHierarchyCut (((s : C0), (t : C0)), u)) : X0) =
        hamiltonZeroCutParameter ((s, t), u) := by
  rw [hamiltonZeroHierarchyCut_coe]
  rfl

theorem hamiltonOneAnnulusParameter_eq_surface (x : D1) (s : ℝ) :
    ((latticeHandleDomainEquiv (Fin 1) (Fin 2) L1).symm
      (hamiltonOneHierarchyAnnulus (x, (s : C1))) : X1) =
        hamiltonOneAnnulusParameter ((x : V1), s) := by
  have he := hamiltonOneHierarchyCut_coe x s 0
  rw [(hamiltonOneHierarchyCut_endpoints (x, (s : C1))).1] at he
  rw [he]
  rfl

theorem hamiltonOneCutParameter_eq_cut (x : D1) (s t : ℝ) :
    ((latticeHandleDomainEquiv (Fin 1) (Fin 2) L1).symm
      (hamiltonOneHierarchyCut ((x, (s : C1)), t)) : X1) =
        hamiltonOneCutParameter (((x : V1), s), t) := by
  rw [hamiltonOneHierarchyCut_coe]
  rfl

theorem StandardLatticeHandleAtlas.polyhedralPL_zeroTorusParameter
    {β : Type*} {d : β → OpenPartialHomeomorph X0 (Fin 3 → ℝ)}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d) :
    PolyhedralPLInCharts d hamiltonZeroTorusParameter (Icc 0 p0 ×ˢ Icc 0 p0) := by
  let v : (ℝ × ℝ) →L[ℝ] (Fin 3 → ℝ) :=
    ContinuousLinearMap.pi ![ContinuousLinearMap.fst ℝ ℝ ℝ,
      ContinuousLinearMap.snd ℝ ℝ ℝ, 0]
  let a : (ℝ × ℝ) →ᴬ[ℝ] ((Fin 0 ⊕ Fin 3) → ℝ) :=
    (ContinuousLinearEquiv.sumPiEquivProdPi ℝ (Fin 0) (Fin 3)
      (fun _ => ℝ)).symm.toContinuousAffineEquiv.toContinuousAffineMap.comp
        ((0 : (ℝ × ℝ) →L[ℝ] V0).prod v).toContinuousAffineMap
  have hI := isFinitePLBallPair_Icc (by norm_num : (0 : ℝ) < p0)
  have hp := hd.polyhedralPL_projection (finiteAffine_on_ballPair (hI.prod hI) a)
  have he : (latticeCoordinateProjection (Fin 0) (Fin 3) L0 ∘ a) =
      hamiltonZeroTorusParameter := by
    funext z
    apply Prod.ext
    · rfl
    · apply congrArg QuotientAddGroup.mk
      funext i
      fin_cases i <;> rfl
  rwa [he] at hp

theorem StandardLatticeHandleAtlas.polyhedralPL_zeroCutParameter
    {β : Type*} {d : β → OpenPartialHomeomorph X0 (Fin 3 → ℝ)}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d) :
    PolyhedralPLInCharts d hamiltonZeroCutParameter
      ((Icc 0 p0 ×ˢ Icc 0 p0) ×ˢ Icc 0 p0) := by
  let fst0 := ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ
  let v : ((ℝ × ℝ) × ℝ) →L[ℝ] (Fin 3 → ℝ) :=
    ContinuousLinearMap.pi ![(ContinuousLinearMap.fst ℝ ℝ ℝ).comp fst0,
      (ContinuousLinearMap.snd ℝ ℝ ℝ).comp fst0,
      ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ]
  let a : ((ℝ × ℝ) × ℝ) →ᴬ[ℝ] ((Fin 0 ⊕ Fin 3) → ℝ) :=
    (ContinuousLinearEquiv.sumPiEquivProdPi ℝ (Fin 0) (Fin 3)
      (fun _ => ℝ)).symm.toContinuousAffineEquiv.toContinuousAffineMap.comp
        ((0 : ((ℝ × ℝ) × ℝ) →L[ℝ] V0).prod v).toContinuousAffineMap
  have hI := isFinitePLBallPair_Icc (by norm_num : (0 : ℝ) < p0)
  have hp := hd.polyhedralPL_projection
    (finiteAffine_on_ballPair ((hI.prod hI).prod hI) a)
  have he : (latticeCoordinateProjection (Fin 0) (Fin 3) L0 ∘ a) =
      hamiltonZeroCutParameter := by
    funext z
    apply Prod.ext
    · rfl
    · apply congrArg QuotientAddGroup.mk
      funext i
      fin_cases i <;> rfl
  rwa [he] at hp

theorem StandardLatticeHandleAtlas.polyhedralPL_oneAnnulusParameter
    {β : Type*} {d : β → OpenPartialHomeomorph X1 (Fin 3 → ℝ)}
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L1 d) :
    PolyhedralPLInCharts d hamiltonOneAnnulusParameter (D1 ×ˢ Icc 0 p1) := by
  let v : (V1 × ℝ) →L[ℝ] (Fin 2 → ℝ) :=
    ContinuousLinearMap.pi ![ContinuousLinearMap.snd ℝ V1 ℝ, 0]
  let a : (V1 × ℝ) →ᴬ[ℝ] ((Fin 1 ⊕ Fin 2) → ℝ) :=
    (ContinuousLinearEquiv.sumPiEquivProdPi ℝ (Fin 1) (Fin 2)
      (fun _ => ℝ)).symm.toContinuousAffineEquiv.toContinuousAffineMap.comp
        ((ContinuousLinearMap.fst ℝ V1 ℝ).prod v).toContinuousAffineMap
  have hS := (isFinitePLBallPair_unit_cube (ι := Fin 1)).prod
    (isFinitePLBallPair_Icc (by norm_num : (0 : ℝ) < p1))
  have hp := hd.polyhedralPL_projection (finiteAffine_on_ballPair hS a)
  have he : (latticeCoordinateProjection (Fin 1) (Fin 2) L1 ∘ a) =
      hamiltonOneAnnulusParameter := by
    funext z
    apply Prod.ext
    · rfl
    · apply congrArg QuotientAddGroup.mk
      funext i
      fin_cases i <;> rfl
  rwa [he] at hp

theorem StandardLatticeHandleAtlas.polyhedralPL_oneCutParameter
    {β : Type*} {d : β → OpenPartialHomeomorph X1 (Fin 3 → ℝ)}
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L1 d) :
    PolyhedralPLInCharts d hamiltonOneCutParameter ((D1 ×ˢ Icc 0 p1) ×ˢ Icc 0 p1) := by
  let fst0 := ContinuousLinearMap.fst ℝ (V1 × ℝ) ℝ
  let v : ((V1 × ℝ) × ℝ) →L[ℝ] (Fin 2 → ℝ) :=
    ContinuousLinearMap.pi ![(ContinuousLinearMap.snd ℝ V1 ℝ).comp fst0,
      ContinuousLinearMap.snd ℝ (V1 × ℝ) ℝ]
  let a : ((V1 × ℝ) × ℝ) →ᴬ[ℝ] ((Fin 1 ⊕ Fin 2) → ℝ) :=
    (ContinuousLinearEquiv.sumPiEquivProdPi ℝ (Fin 1) (Fin 2)
      (fun _ => ℝ)).symm.toContinuousAffineEquiv.toContinuousAffineMap.comp
        (((ContinuousLinearMap.fst ℝ V1 ℝ).comp fst0).prod v).toContinuousAffineMap
  have hI := isFinitePLBallPair_Icc (by norm_num : (0 : ℝ) < p1)
  have hS := ((isFinitePLBallPair_unit_cube (ι := Fin 1)).prod hI).prod hI
  have hp := hd.polyhedralPL_projection (finiteAffine_on_ballPair hS a)
  have he : (latticeCoordinateProjection (Fin 1) (Fin 2) L1 ∘ a) =
      hamiltonOneCutParameter := by
    funext z
    apply Prod.ext
    · rfl
    · apply congrArg QuotientAddGroup.mk
      funext i
      fin_cases i <;> rfl
  rwa [he] at hp

end PoincareConjecture.M76
