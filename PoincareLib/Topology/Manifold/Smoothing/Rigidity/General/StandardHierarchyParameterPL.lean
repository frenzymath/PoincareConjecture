import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Levels.StandardHierarchyCuts
import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Handles.HamiltonStandardQuotientPL
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Products.AlexanderBaseProductBall
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Arcs.FinitePLIntervals
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Handles.HamiltonHandleCubeBall

/-!
# Whole standard-atlas parameter certificates for the target cuts

The literal affine lifts give the original quotient maps on complete
closed period boxes, including all faces and corners. Finite carriers
come from actual interval and cube ball pairs. See Hamilton1976,
pp.65--68, and rigidity050, sections3--4. No global injectivity of a
closed period box is asserted.
-/

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareMT.M76

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

/-- The complete first torus parameter in the original quotient
ambient. The two period edges are not deleted. See050, section3. -/
def hamiltonZeroTorusParameter (z : ℝ × ℝ) : X0 :=
  (0, QuotientAddGroup.mk ![z.1, z.2, 0])

/-- The complete first three-torus cut parameter uses the same
three original quotient coordinates. See rigidity050, section3. -/
def hamiltonZeroCutParameter (z : (ℝ × ℝ) × ℝ) : X0 :=
  (0, QuotientAddGroup.mk ![z.1.1, z.1.2, z.2])

/-- The complete annulus parameter retains the original bounded
vector and quotient circle, including the full rim. See050. -/
def hamiltonOneAnnulusParameter (z : V1 × ℝ) : X1 :=
  (z.1, QuotientAddGroup.mk ![z.2, 0])

/-- The complete annulus cut parameter retains both original
quotient coordinates and the original bounded vector. See050. -/
def hamiltonOneCutParameter (z : (V1 × ℝ) × ℝ) : X1 :=
  (z.1.1, QuotientAddGroup.mk ![z.1.2, z.2])

/-- This literal period rectangle parametrizes the same original
target torus, through the fixed domain identification. See050. -/
theorem hamiltonZeroTorusParameter_eq_surface (s t : ℝ) :
    ((latticeHandleDomainEquiv (Fin 0) (Fin 3) L0).symm
      (hamiltonZeroHierarchyTorus ((s : C0), (t : C0))) : X0) =
        hamiltonZeroTorusParameter (s, t) := by
  have he := hamiltonZeroHierarchyCut_coe s t 0
  rw [(hamiltonZeroHierarchyCut_endpoints ((s : C0), (t : C0))).1] at he
  rw [he]
  rfl

/-- Every real parameter gives the same original complete cut
value as the topological product cut. See050, section3. -/
theorem hamiltonZeroCutParameter_eq_cut (s t u : ℝ) :
    ((latticeHandleDomainEquiv (Fin 0) (Fin 3) L0).symm
      (hamiltonZeroHierarchyCut (((s : C0), (t : C0)), u)) : X0) =
        hamiltonZeroCutParameter ((s, t), u) := by
  rw [hamiltonZeroHierarchyCut_coe]
  rfl

/-- The annulus rectangle gives the same actual surface values
at every original bounded point and real circle parameter. See050. -/
theorem hamiltonOneAnnulusParameter_eq_surface (x : D1) (s : ℝ) :
    ((latticeHandleDomainEquiv (Fin 1) (Fin 2) L1).symm
      (hamiltonOneHierarchyAnnulus (x, (s : C1))) : X1) =
        hamiltonOneAnnulusParameter ((x : V1), s) := by
  have he := hamiltonOneHierarchyCut_coe x s 0
  rw [(hamiltonOneHierarchyCut_endpoints (x, (s : C1))).1] at he
  rw [he]
  rfl

/-- The whole annulus cut box has precisely the same original
ambient values as the topological cut. See050, section4. -/
theorem hamiltonOneCutParameter_eq_cut (x : D1) (s t : ℝ) :
    ((latticeHandleDomainEquiv (Fin 1) (Fin 2) L1).symm
      (hamiltonOneHierarchyCut ((x, (s : C1)), t)) : X1) =
        hamiltonOneCutParameter (((x : V1), s), t) := by
  rw [hamiltonOneHierarchyCut_coe]
  rfl

/-- The standard atlas certifies the full closed period rectangle
of the first torus, with every edge and corner. See050, section3. -/
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

/-- The whole closed period cube of the first torus cut is PL
in the same supplied standard atlas. See rigidity050, section3. -/
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

/-- The full original annulus rectangle is PL in every supplied
standard target atlas, including its entire rim. See050, section4. -/
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

/-- The entire closed annulus-cut box is PL in the original
standard atlas, retaining all old and new faces. See050, section4. -/
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

end PoincareMT.M76
